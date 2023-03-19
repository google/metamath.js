include "cv.mm"
include "wrel.mm"
include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "cin.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cps.mm"
include "releq.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqtrd.mm"
include "id.mm"
include "sseq12d.mm"
include "cnveq.mm"
include "ineq12d.mm"
include "unieq.mm"
include "unieqd.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "df-ps.mm"
include "elab2g.mm"

theorem isps
  let cA: class A
  let cR: class R
  let vr: setvar r


  assert |- ( R e. A -> ( R e. PosetRel <-> ( Rel R /\ ( R o. R ) C_ R /\ ( R i^i `' R ) = ( _I |` U. U. R ) ) ) )

  proof
    vr
    cv
    #
    wrel
    #
    @0
    @0
    ccom
    #
    @0
    wss
    #
    @0
    @0
    ccnv
    #
    cin
    #
    cid
    @0
    cuni
    #
    cuni
    #
    cres
    #
    wceq
    #
    w3a
    cR
    wrel
    #
    cR
    cR
    ccom
    #
    cR
    wss
    #
    cR
    cR
    ccnv
    #
    cin
    #
    cid
    cR
    cuni
    #
    cuni
    #
    cres
    #
    wceq
    #
    w3a
    vr
    cR
    cps
    cA
    @0
    cR
    wceq
    #
    @1
    @10
    @3
    @12
    @9
    @18
    @0
    cR
    releq
    @19
    @2
    @11
    @0
    cR
    @19
    @2
    cR
    @0
    ccom
    @11
    @0
    cR
    @0
    coeq1
    @0
    cR
    cR
    coeq2
    eqtrd
    @19
    id
    #
    sseq12d
    @19
    @5
    @14
    @8
    @17
    @19
    @0
    cR
    @4
    @13
    @20
    @0
    cR
    cnveq
    ineq12d
    @19
    @7
    @16
    cid
    @19
    @6
    @15
    @0
    cR
    unieq
    unieqd
    reseq2d
    eqeq12d
    3anbi123d
    vr
    df-ps
    elab2g
end
