include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cpg.mm"
include "wss.mm"
include "c1st.mm"
include "cfv.mm"
include "cpw.mm"
include "c2nd.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "elpglem1.mm"
include "elpglem2.mm"
include "impbii.mm"
include "anbi2i.mm"
include "cmpt.mm"
include "df-pg.mm"
include "elsetrecs.mm"
include "elpglem3.mm"
include "bitri.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem elpg
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( A e. Pg <-> ( A e. ( _V X. _V ) /\ ( 1st ` A ) C_ Pg /\ ( 2nd ` A ) C_ Pg ) )

  proof
    cA
    cvv
    cvv
    cxp
    wcel
    #
    vx
    cv
    #
    cpg
    wss
    #
    cA
    c1st
    cfv
    #
    @1
    cpw
    #
    wcel
    cA
    c2nd
    cfv
    #
    @4
    wcel
    wa
    wa
    vx
    wex
    #
    wa
    #
    @0
    @3
    cpg
    wss
    #
    @5
    cpg
    wss
    #
    wa
    #
    wa
    cA
    cpg
    wcel
    #
    @0
    @8
    @9
    w3a
    @6
    @10
    @0
    @6
    @10
    vx
    cA
    elpglem1
    vx
    cA
    elpglem2
    impbii
    anbi2i
    @11
    @2
    cA
    @1
    vy
    cvv
    vy
    cv
    cpw
    #
    @12
    cxp
    cmpt
    #
    cfv
    wcel
    wa
    vx
    wex
    @7
    vx
    cA
    cpg
    @13
    vy
    df-pg
    elsetrecs
    vx
    vy
    cA
    elpglem3
    bitri
    @0
    @8
    @9
    3anass
    3bitr4i
end
