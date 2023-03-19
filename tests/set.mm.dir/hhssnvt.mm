include "csh.mm"
include "wcel.mm"
include "cnv.mm"
include "cva.mm"
include "c0h.mm"
include "cif.mm"
include "cxp.mm"
include "cres.mm"
include "csm.mm"
include "cc.mm"
include "cop.mm"
include "cno.mm"
include "wceq.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "eqtrd.mm"
include "reseq2d.mm"
include "opeq12d.mm"
include "reseq2.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "eqid.mm"
include "h0elsh.mm"
include "elimel.mm"
include "hhssnv.mm"
include "dedth.mm"

theorem hhssnvt
  let cH: class H
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hhssnvt.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.


  assert |- ( H e. SH -> W e. NrmCVec )

  proof
    cH
    csh
    wcel
    #
    cW
    cnv
    wcel
    cva
    @0
    cH
    c0h
    cif
    #
    @1
    cxp
    #
    cres
    #
    csm
    cc
    @1
    cxp
    #
    cres
    #
    cop
    #
    cno
    @1
    cres
    #
    cop
    #
    cnv
    wcel
    cH
    c0h
    cH
    @1
    wceq
    #
    cW
    @8
    cnv
    @9
    cW
    cva
    cH
    cH
    cxp
    #
    cres
    #
    csm
    cc
    cH
    cxp
    #
    cres
    #
    cop
    #
    cno
    cH
    cres
    #
    cop
    @8
    hhssnvt.1
    @9
    @14
    @6
    @15
    @7
    @9
    @11
    @3
    @13
    @5
    @9
    @10
    @2
    cva
    @9
    @10
    @1
    cH
    cxp
    @2
    cH
    @1
    cH
    xpeq1
    cH
    @1
    @1
    xpeq2
    eqtrd
    reseq2d
    @9
    @12
    @4
    csm
    cH
    @1
    cc
    xpeq2
    reseq2d
    opeq12d
    cH
    @1
    cno
    reseq2
    opeq12d
    syl5eq
    eleq1d
    @1
    @8
    @8
    eqid
    cH
    c0h
    csh
    h0elsh
    elimel
    hhssnv
    dedth
end
