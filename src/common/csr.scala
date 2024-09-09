// See LICENSE for license details.

// TODO: add timeh, cycleh, counth, instreh counters for the full RV32I experience.
// NOTE: This is mostly a copy from the Berkeley Rocket-chip csr file. It is
//       overkill for a small, embedded processor.

package Common


import chisel3._
import collection.mutable.LinkedHashMap
import chisel3.util._
import Util._
import Instructions._


import Common.Constants._
import scala.math._

class MStatus extends Bundle {
    // not truly part of mstatus, but convenient
  val debug = Bool()
  val prv = UInt(PRV.SZ.W) // not truly part of mstatus, but convenient
  val sd = Bool()
  val zero1 = UInt(8.W)
  val tsr = Bool()
  val tw = Bool()
  val tvm = Bool()
  val mxr = Bool()
  val sum = Bool()
  val mprv = Bool()
  val xs = UInt(2.W)
  val fs = UInt(2.W)
  val mpp = UInt(2.W)
  val hpp = UInt(2.W)
  val spp = UInt(1.W)
  val mpie = Bool()
  val hpie = Bool()
  val spie = Bool()
  val upie = Bool()
  val mie = Bool()
  val hie = Bool()
  val sie = Bool()
  val uie = Bool()
}

object PRV
{
  val SZ = 2
  val U = 0
  val S = 1
  val H = 2
  val M = 3
}

class MIP extends Bundle {
  val zero2 = Bool()
  val debug = Bool() // keep in sync with CSR.debugIntCause
  val zero1 = Bool()
  val rocc = Bool()
  val meip = Bool()
  val heip = Bool()
  val seip = Bool()
  val ueip = Bool()
  val mtip = Bool()
  val htip = Bool()
  val stip = Bool()
  val utip = Bool()
  val msip = Bool()
  val hsip = Bool()
  val ssip = Bool()
  val usip = Bool()
}

object CSR
{
  // commands
  val SZ = 3.W
  val X = 0.asUInt(SZ)
  val N = 0.asUInt(SZ)
  val W = 1.asUInt(SZ)
  val S = 2.asUInt(SZ)
  val C = 3.asUInt(SZ)
  val I = 4.asUInt(SZ)
  val R = 5.asUInt(SZ)

  val ADDRSZ = 12
}

class CSRFileIO(implicit val conf: SodorConfiguration) extends Bundle {
  val rw = new Bundle {
    val cmd = Input(UInt(CSR.SZ))
    val rdata = Output(UInt(conf.xprlen.W))
    val wdata = Input(UInt(conf.xprlen.W))
  }

  val eret = Output(Bool())

  val decode = new Bundle {
    val csr = Input(UInt(CSR.ADDRSZ.W))
  }

  val evec = Output(UInt(conf.xprlen.W))
  val exception = Input(Bool())
  val pc = Input(UInt(conf.xprlen.W))
}

class CSRFile(implicit val conf: SodorConfiguration) extends Module
{
  val io = IO(new CSRFileIO)
  io := DontCare

  val reset_mstatus = WireInit(0.U.asTypeOf(new MStatus()))
  reset_mstatus.mpp := PRV.M
  reset_mstatus.prv := PRV.M
  val reg_mstatus = RegInit(reset_mstatus)
  val reg_mepc = Reg(UInt(conf.xprlen.W))
  val reg_mcause = Reg(UInt(conf.xprlen.W))
  val reg_mtval = Reg(UInt(conf.xprlen.W))
  val reg_mscratch = Reg(UInt(conf.xprlen.W))
  val reg_medeleg = Reg(UInt(conf.xprlen.W))

  val reg_mip = RegInit(0.U.asTypeOf(new MIP()))
  val reg_mie = RegInit(0.U.asTypeOf(new MIP()))
  val reg_mtvec = Reg(UInt(conf.xprlen.W))

  val system_insn = io.rw.cmd === CSR.I
  val cpu_ren = io.rw.cmd =/= CSR.N && !system_insn

  val read_mstatus = reg_mstatus.asUInt()

  val read_mapping = collection.mutable.LinkedHashMap[Int,Bits](
    CSRs.misa -> 0.U,
    CSRs.mstatus -> read_mstatus,
    CSRs.mtvec -> MTVEC.U,
    CSRs.mip -> reg_mip.asUInt(),
    CSRs.mie -> reg_mie.asUInt(),
    CSRs.mscratch -> reg_mscratch,
    CSRs.mepc -> reg_mepc,
    CSRs.mtval -> reg_mtval,
    CSRs.mcause -> reg_mcause,
    CSRs.medeleg -> reg_medeleg)

  val decoded_addr = read_mapping map { case (k, v) => k -> (io.decode.csr === k) }

  val priv_sufficient = reg_mstatus.prv >= io.decode.csr(9,8)
  val read_only = io.decode.csr(11,10).andR
  val cpu_wen = cpu_ren && io.rw.cmd =/= CSR.R && priv_sufficient
  val wen = cpu_wen && !read_only
  val wdata = readModifyWriteCSR(io.rw.cmd, io.rw.rdata, io.rw.wdata)

  val opcode = 1.U << io.decode.csr(2,0)
  val insn_call = system_insn && opcode(0)
  val insn_break = system_insn && opcode(1)
  val insn_ret = system_insn && opcode(2) && priv_sufficient
  val insn_wfi = system_insn && opcode(5) && priv_sufficient

  io.eret := insn_call || insn_break || insn_ret

  // ILLEGAL INSTR
  // TODO: Support misaligned address exceptions
  when (io.exception) {
    reg_mcause := Causes.illegal_instruction
  }

  assert(PopCount(insn_ret :: io.exception :: Nil) <= 1, "these conditions must be mutually exclusive")

  reg_mip.mtip := true

  // io.evec must be held stable for more than one cycle for the
  // microcoded code to correctly redirect the PC on exceptions
  io.evec := 0x80000004L.U

  //MRET
  when (insn_ret && !io.decode.csr(10)) {
    reg_mstatus.mie := reg_mstatus.mpie
    reg_mstatus.mpie := true
    io.evec := reg_mepc
  }

  //ECALL
  when(insn_call){
    reg_mcause := reg_mstatus.prv + Causes.user_ecall
  }

  //EBREAK
  when(insn_break){
    reg_mcause := Causes.breakpoint
  }

  when (io.exception || insn_call || insn_break) {
    reg_mepc := io.pc
  }

  io.rw.rdata := Mux1H(for ((k, v) <- read_mapping) yield decoded_addr(k) -> v)

  when (wen) {

    when (decoded_addr(CSRs.mstatus)) {
      val new_mstatus = wdata.asTypeOf(new MStatus())
      reg_mstatus.mie := new_mstatus.mie
      reg_mstatus.mpie := new_mstatus.mpie
    }
    when (decoded_addr(CSRs.mip)) {
      val new_mip = wdata.asTypeOf(new MIP())
      reg_mip.msip := new_mip.msip
    }
    when (decoded_addr(CSRs.mie)) {
      val new_mie = wdata.asTypeOf(new MIP())
      reg_mie.msip := new_mie.msip
      reg_mie.mtip := new_mie.mtip
    }

    when (decoded_addr(CSRs.mepc))     { reg_mepc := (wdata(conf.xprlen-1,0) >> 2.U) << 2.U }
    when (decoded_addr(CSRs.mscratch)) { reg_mscratch := wdata }
    when (decoded_addr(CSRs.mcause))   { reg_mcause := wdata & ((BigInt(1) << (conf.xprlen-1)) + 31).U /* only implement 5 LSBs and MSB */ }
    when (decoded_addr(CSRs.mtval))    { reg_mtval := wdata(conf.xprlen-1,0) }
    when (decoded_addr(CSRs.medeleg))    { reg_medeleg := wdata(conf.xprlen-1,0) }

  }

  def readModifyWriteCSR(cmd: UInt, rdata: UInt, wdata: UInt) =
    (Mux(cmd.isOneOf(CSR.S, CSR.C), rdata, 0.U) | wdata) & ~Mux(cmd === CSR.C, wdata, 0.U)
}
