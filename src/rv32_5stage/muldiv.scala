// See LICENSE.Berkeley for license details.
// See LICENSE.SiFive for license details.

package Sodor
{

import chisel3._
import chisel3.util._


import Constants._
import Common._


class MultiplierReq extends Bundle {
  val fn = UInt(4.W)
  val in1 = UInt(32.W)
  val in2 = UInt(32.W)
}

class MultiplierResp extends Bundle {
  val data = Bits(32.W)
}

class MultiplierIO() extends Bundle {
  val req = Flipped(Decoupled(new MultiplierReq()))
  val kill = Input(Bool())
  val resp = Decoupled(new MultiplierResp())
}

class MulDiv() extends Module {
  val io = IO(new MultiplierIO())
  val w = io.req.bits.in1.getWidth
  val mulw = w
  val fastMulW = w/2 > 1 && w % 2 == 0
 
  val s_ready :: s_neg_inputs :: s_mul :: s_div :: s_dummy :: s_neg_output :: s_done_mul :: s_done_div :: Nil = Enum(8)
  val state = RegInit(s_ready)
 
  val req = Reg(chiselTypeOf(io.req.bits))
  val count = Reg(UInt(6.W))
  val neg_out = Reg(Bool())
  val isHi = Reg(Bool())
  val resHi = Reg(Bool())
  val divisor = Reg(Bits((w+1).W)) // div only needs w bits
  val remainder = Reg(Bits((2*mulw+2).W)) // div only needs 2*w+1 bits

  val Y = true.B
  val N = false.B
  val decodeTable = Seq(
    MDU_MUL    -> Seq(Y, N, N, N),
    MDU_MULH   -> Seq(Y, Y, Y, Y),
    MDU_MULHU  -> Seq(Y, Y, N, N),
    MDU_MULHSU -> Seq(Y, Y, Y, N),
    MDU_DIV    -> Seq(N, N, Y, Y),
    MDU_REM    -> Seq(N, Y, Y, Y),
    MDU_DIVU   -> Seq(N, N, N, N),
    MDU_REMU   -> Seq(N, Y, N, N)
  )
  
  val cmdMul     = MuxLookup(io.req.bits.fn, N, decodeTable.map(x => (x._1, x._2(0))))
  val cmdHi      = MuxLookup(io.req.bits.fn, N, decodeTable.map(x => (x._1, x._2(1))))
  val lhsSigned  = MuxLookup(io.req.bits.fn, N, decodeTable.map(x => (x._1, x._2(2))))
  val rhsSigned  = MuxLookup(io.req.bits.fn, N, decodeTable.map(x => (x._1, x._2(3))))

  require(w == 32 || w == 64)

  def sext(x: Bits, signed: Bool) = {
    val sign = signed && x(w-1)
    val hi = x(w-1,w/2)
    (Cat(hi, x(w/2-1,0)), sign)
  }
  val (lhs_in, lhs_sign) = sext(io.req.bits.in1, lhsSigned)
  val (rhs_in, rhs_sign) = sext(io.req.bits.in2, rhsSigned)
  
  val subtractor = remainder(2*w,w) - divisor
  val result = Mux(resHi, remainder(2*w, w+1), remainder(w-1, 0))
  val negated_remainder = -result

  when (state === s_neg_inputs) {
    when (remainder(w-1)) {
      remainder := negated_remainder
    }
    when (divisor(w-1)) {
      divisor := subtractor
    }
    state := s_div
  }

  when (state === s_neg_output) {
    remainder := negated_remainder
    state := s_done_div
    resHi := false.B
  }

  when (state === s_mul) {
    val mulReg = Cat(remainder(2*mulw+1,w+1),remainder(w-1,0))
    val mplierSign = remainder(w)
    val mplier = mulReg(mulw-1,0)
    val accum = mulReg(2*mulw,mulw).asSInt
    val mpcand = divisor.asSInt
    val prod = Cat(mplierSign, mplier(0, 0)).asSInt * mpcand + accum
    val nextMulReg = Cat(prod, mplier(mulw-1, 1))
    val nextMplierSign = count === (mulw-2).U && neg_out

    val eOutMask = ((BigInt(-1) << mulw).S >> (count)(log2Up(mulw)-1,0))(mulw-1,0)
    val eOut = count =/= (mulw).U && count =/= 0.U && !isHi && (mplier & ~eOutMask) === 0.U
    val eOutRes = (mulReg >> (mulw.U - count)(log2Up(mulw)-1,0))
    val nextMulReg1 = Cat(nextMulReg(2*mulw,mulw), Mux(eOut, eOutRes, nextMulReg)(mulw-1,0))
    remainder := Cat(nextMulReg1 >> w, nextMplierSign, nextMulReg1(w-1,0))

    count := count + 1.U
    when (eOut || count === (mulw-1).U) {
      state := s_done_mul
      resHi := isHi
    }
  }

  when (state === s_div) {
    val unrolls = ((0 until 1) scanLeft remainder) { case (rem, i) =>
      // the special case for iteration 0 is to save HW, not for correctness
      val difference = if (i == 0) subtractor else rem(2*w,w) - divisor(w-1,0)
      val less = difference(w)
      Cat(Mux(less, rem(2*w-1,w), difference(w-1,0)), rem(w-1,0), !less)
    }.tail

    remainder := unrolls.last
    when (count === w.U) {
      state := Mux(neg_out, s_neg_output, s_done_div)
      resHi := isHi
    }
    count := count + 1.U

    val divby0 = count === 0.U && !subtractor(w)
    when (divby0 && !isHi) { neg_out := false.B }
  }

  when (io.resp.fire || io.kill) {
    state := s_ready
  }
  when (io.req.fire) {
    state := Mux(cmdMul, s_mul, Mux(lhs_sign || rhs_sign, s_neg_inputs, s_div))
    isHi := cmdHi
    resHi := false.B
    count := 0.U
    neg_out := Mux(cmdHi, lhs_sign, lhs_sign =/= rhs_sign)
    divisor := Cat(rhs_sign, rhs_in)
    remainder := lhs_in
    req := io.req.bits
  }

  val outMul = (state & (s_done_mul ^ s_done_div)) === (s_done_mul & ~s_done_div)
  val loOut = result(w/2-1,0)
  val hiOut = result(w-1,w/2)

  io.resp.bits.data := Cat(hiOut, loOut)
  io.resp.valid := (state === s_done_mul || state === s_done_div)
  io.req.ready := state === s_ready
}

}
