include "cdir.mm"
include "wcel.mm"
include "wbr.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "eqid.mm"
include "wb.mm"
include "resieq.mm"
include "anidms.mm"
include "mpbiri.mm"
include "cuni.mm"
include "cdm.mm"
include "dirdm.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "wrel.mm"
include "wss.mm"
include "wa.mm"
include "ccom.mm"
include "cxp.mm"
include "ccnv.mm"
include "isdir.mm"
include "ibi.mm"
include "simpld.mm"
include "simprd.mm"
include "eqsstrd.mm"
include "ssbrd.mm"
include "syl5.mm"
include "imp.mm"

theorem dirref
  let cA: class A
  let cR: class R
  let cX: class X
  assume dirref.1: |- X = dom R


  assert |- ( ( R e. DirRel /\ A e. X ) -> A R A )

  proof
    cR
    cdir
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cA
    cR
    wbr
    #
    @1
    cA
    cA
    cid
    cX
    cres
    #
    wbr
    #
    @0
    @2
    @1
    @4
    cA
    cA
    wceq
    #
    cA
    eqid
    @1
    @4
    @5
    wb
    cX
    cA
    cA
    resieq
    anidms
    mpbiri
    @0
    @3
    cR
    cA
    cA
    @0
    @3
    cid
    cR
    cuni
    cuni
    #
    cres
    #
    cR
    @0
    cX
    @6
    cid
    @0
    cX
    cR
    cdm
    @6
    dirref.1
    cR
    dirdm
    syl5eq
    reseq2d
    @0
    cR
    wrel
    #
    @7
    cR
    wss
    #
    @0
    @8
    @9
    wa
    #
    cR
    cR
    ccom
    cR
    wss
    @6
    @6
    cxp
    cR
    ccnv
    cR
    ccom
    wss
    wa
    #
    @0
    @10
    @11
    wa
    @6
    cR
    cdir
    @6
    eqid
    isdir
    ibi
    simpld
    simprd
    eqsstrd
    ssbrd
    syl5
    imp
end
