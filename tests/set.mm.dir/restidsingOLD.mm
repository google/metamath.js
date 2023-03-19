include "cid.mm"
include "csn.mm"
include "cres.mm"
include "cxp.mm"
include "relres.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "df-br.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "simpr.mm"
include "wceq.mm"
include "velsn.mm"
include "wi.mm"
include "cvv.mm"
include "vex.mm"
include "ideqg.mm"
include "biimpd.mm"
include "ax-mp.mm"
include "eqtr2.mm"
include "ex.mm"
include "syl6ibr.mm"
include "syl.mm"
include "syl5bi.mm"
include "imp.mm"
include "jca.mm"
include "eqtr3.mm"
include "ideq.mm"
include "equcom.mm"
include "bitri.mm"
include "sylibr.mm"
include "sylbi.mm"
include "com12.mm"
include "simpl.mm"
include "impbii.mm"
include "opelres.mm"
include "opelxp.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem restidsingOLD
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( _I |` { A } ) = ( { A } X. { A } )

  proof
    vx
    vy
    cid
    cA
    csn
    #
    cres
    #
    @0
    @0
    cxp
    #
    cid
    @0
    relres
    @0
    @0
    relxp
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cid
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    #
    @7
    @4
    @0
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    @5
    @2
    wcel
    @8
    @3
    @4
    cid
    wbr
    #
    @7
    wa
    #
    @10
    @6
    @11
    @7
    @11
    @6
    @3
    @4
    cid
    df-br
    bicomi
    anbi1i
    @12
    @10
    @12
    @7
    @9
    @11
    @7
    simpr
    @11
    @7
    @9
    @7
    @3
    cA
    wceq
    #
    @11
    @9
    vx
    cA
    velsn
    #
    @11
    @3
    @4
    wceq
    #
    @13
    @9
    wi
    @4
    cvv
    wcel
    #
    @11
    @15
    wi
    vy
    vex
    #
    @16
    @11
    @15
    @3
    @4
    cvv
    ideqg
    biimpd
    ax-mp
    @15
    @13
    @4
    cA
    wceq
    #
    @9
    @15
    @13
    @18
    @3
    @4
    cA
    eqtr2
    ex
    vy
    cA
    velsn
    #
    syl6ibr
    syl
    syl5bi
    imp
    jca
    @10
    @11
    @7
    @7
    @9
    @11
    @7
    @13
    @9
    @11
    wi
    @14
    @9
    @13
    @11
    @9
    @18
    @13
    @11
    wi
    @19
    @18
    @13
    @11
    @18
    @13
    wa
    @4
    @3
    wceq
    #
    @11
    @4
    @3
    cA
    eqtr3
    @11
    @15
    @20
    @3
    @4
    @17
    ideq
    vx
    vy
    equcom
    bitri
    sylibr
    ex
    sylbi
    com12
    sylbi
    imp
    @7
    @9
    simpl
    jca
    impbii
    bitri
    @3
    @4
    cid
    @0
    @17
    opelres
    @3
    @4
    @0
    @0
    opelxp
    3bitr4i
    eqrelriiv
end
