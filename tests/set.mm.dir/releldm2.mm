include "wrel.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "anim2i.mm"
include "id.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "rexlimivw.mm"
include "cop.mm"
include "wex.mm"
include "wb.mm"
include "eldm2g.mm"
include "adantl.mm"
include "cxp.mm"
include "wss.mm"
include "wi.mm"
include "df-rel.mm"
include "ssel.mm"
include "sylbi.mm"
include "imp.mm"
include "op1steq.mm"
include "syl.mm"
include "rexbidva.mm"
include "adantr.mm"
include "rexcom4.mm"
include "risset.mm"
include "exbii.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "bitr4d.mm"
include "pm5.21nd.mm"

theorem releldm2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( Rel A -> ( B e. dom A <-> E. x e. A ( 1st ` x ) = B ) )

  proof
    cA
    wrel
    #
    cB
    cA
    cdm
    #
    wcel
    #
    vx
    cv
    #
    c1st
    cfv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    cB
    cvv
    wcel
    #
    wa
    #
    @2
    @7
    @0
    cB
    @1
    elex
    anim2i
    @6
    @7
    @0
    @5
    @7
    vx
    cA
    @5
    cB
    @4
    cvv
    @5
    id
    @3
    c1st
    fvex
    syl6eqelr
    rexlimivw
    anim2i
    @8
    @2
    cB
    vy
    cv
    cop
    #
    cA
    wcel
    #
    vy
    wex
    #
    @6
    @7
    @2
    @11
    wb
    @0
    vy
    cB
    cA
    cvv
    eldm2g
    adantl
    @8
    @6
    @3
    @9
    wceq
    #
    vy
    wex
    #
    vx
    cA
    wrex
    #
    @11
    @0
    @6
    @14
    wb
    @7
    @0
    @5
    @13
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    wa
    @3
    cvv
    cvv
    cxp
    #
    wcel
    #
    @5
    @13
    wb
    @0
    @15
    @17
    @0
    cA
    @16
    wss
    @15
    @17
    wi
    cA
    df-rel
    cA
    @16
    @3
    ssel
    sylbi
    imp
    vy
    @3
    cB
    cvv
    cvv
    op1steq
    syl
    rexbidva
    adantr
    @14
    @12
    vx
    cA
    wrex
    #
    vy
    wex
    @11
    @12
    vx
    vy
    cA
    rexcom4
    @10
    @18
    vy
    vx
    @9
    cA
    risset
    exbii
    bitr4i
    syl6bb
    bitr4d
    pm5.21nd
end
