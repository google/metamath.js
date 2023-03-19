include "cid.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "wa.mm"
include "wrel.mm"
include "wss.mm"
include "reli.mm"
include "df-rel.mm"
include "mpbi.mm"
include "sseli.mm"
include "cop.mm"
include "1st2nd2.mm"
include "syl.mm"
include "eleq1d.mm"
include "ibi.mm"
include "cv.mm"
include "copab.mm"
include "df-id.mm"
include "eleq2i.mm"
include "fvex.mm"
include "eqeq12.mm"
include "opelopaba.mm"
include "bitri.mm"
include "sylib.mm"
include "jca.mm"
include "biimprd.mm"
include "syl5bir.mm"
include "imp.mm"
include "impbii.mm"

theorem bj-elid
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. _I <-> ( A e. ( _V X. _V ) /\ ( 1st ` A ) = ( 2nd ` A ) ) )

  proof
    cA
    cid
    wcel
    #
    cA
    cvv
    cvv
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    wceq
    #
    wa
    @0
    @2
    @5
    cid
    @1
    cA
    cid
    wrel
    cid
    @1
    wss
    reli
    cid
    df-rel
    mpbi
    sseli
    #
    @0
    @3
    @4
    cop
    #
    cid
    wcel
    #
    @5
    @0
    @8
    @0
    cA
    @7
    cid
    @0
    @2
    cA
    @7
    wceq
    @6
    cA
    cvv
    cvv
    1st2nd2
    #
    syl
    eleq1d
    ibi
    @8
    @7
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    vy
    copab
    #
    wcel
    @5
    cid
    @13
    @7
    vx
    vy
    df-id
    eleq2i
    @12
    @5
    vx
    vy
    @3
    @4
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    @10
    @3
    @11
    @4
    eqeq12
    opelopaba
    bitri
    #
    sylib
    jca
    @2
    @5
    @0
    @5
    @8
    @2
    @0
    @14
    @2
    @0
    @8
    @2
    cA
    @7
    cid
    @9
    eleq1d
    biimprd
    syl5bir
    imp
    impbii
end
