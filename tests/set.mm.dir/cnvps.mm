include "cps.mm"
include "wcel.mm"
include "ccnv.mm"
include "wrel.mm"
include "ccom.mm"
include "wss.mm"
include "cin.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "relcnv.mm"
include "a1i.mm"
include "cnvco.mm"
include "pstr2.mm"
include "cnvss.mm"
include "syl.mm"
include "syl5eqssr.mm"
include "psrel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "ineq2d.mm"
include "incom.mm"
include "syl6eq.mm"
include "psref2.mm"
include "relcnvfld.mm"
include "reseq2d.mm"
include "3eqtrd.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "cnvexg.mm"
include "isps.mm"
include "mpbir3and.mm"

theorem cnvps
  let cR: class R


  assert |- ( R e. PosetRel -> `' R e. PosetRel )

  proof
    cR
    cps
    wcel
    #
    cR
    ccnv
    #
    cps
    wcel
    #
    @1
    wrel
    #
    @1
    @1
    ccom
    #
    @1
    wss
    #
    @1
    @1
    ccnv
    #
    cin
    #
    cid
    @1
    cuni
    cuni
    #
    cres
    #
    wceq
    #
    @3
    @0
    cR
    relcnv
    a1i
    @0
    @4
    cR
    cR
    ccom
    #
    ccnv
    #
    @1
    cR
    cR
    cnvco
    @0
    @11
    cR
    wss
    @12
    @1
    wss
    cR
    pstr2
    @11
    cR
    cnvss
    syl
    syl5eqssr
    @0
    @7
    cR
    @1
    cin
    #
    cid
    cR
    cuni
    cuni
    #
    cres
    @9
    @0
    @7
    @1
    cR
    cin
    @13
    @0
    @6
    cR
    @1
    @0
    cR
    wrel
    #
    @6
    cR
    wceq
    cR
    psrel
    #
    cR
    dfrel2
    sylib
    ineq2d
    @1
    cR
    incom
    syl6eq
    cR
    psref2
    @0
    @14
    @8
    cid
    @0
    @15
    @14
    @8
    wceq
    @16
    cR
    relcnvfld
    syl
    reseq2d
    3eqtrd
    @0
    @1
    cvv
    wcel
    @2
    @3
    @5
    @10
    w3a
    wb
    cR
    cps
    cnvexg
    cvv
    @1
    isps
    syl
    mpbir3and
end
