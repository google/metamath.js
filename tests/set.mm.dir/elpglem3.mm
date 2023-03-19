include "cv.mm"
include "cpg.mm"
include "wss.mm"
include "cvv.mm"
include "cpw.mm"
include "cxp.mm"
include "cmpt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "c1st.mm"
include "c2nd.mm"
include "wceq.mm"
include "vex.mm"
include "weq.mm"
include "pweq.mm"
include "sqxpeqd.mm"
include "eqid.mm"
include "pwex.mm"
include "xpex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "elxp7.mm"
include "bitri.mm"
include "anbi2i.mm"
include "an12.mm"
include "exbii.mm"
include "19.42v.mm"

theorem elpglem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k

  disjoint A x
  disjoint x y
  disjoint k x
  assert |- ( E. x ( x C_ Pg /\ A e. ( ( y e. _V |-> ( ~P y X. ~P y ) ) ` x ) ) <-> ( A e. ( _V X. _V ) /\ E. x ( x C_ Pg /\ ( ( 1st ` A ) e. ~P x /\ ( 2nd ` A ) e. ~P x ) ) ) )

  proof
    vx
    cv
    #
    cpg
    wss
    #
    cA
    @0
    vy
    cvv
    vy
    cv
    #
    cpw
    #
    @3
    cxp
    #
    cmpt
    #
    cfv
    #
    wcel
    #
    wa
    #
    vx
    wex
    cA
    cvv
    cvv
    cxp
    wcel
    #
    @1
    cA
    c1st
    cfv
    @0
    cpw
    #
    wcel
    cA
    c2nd
    cfv
    @10
    wcel
    wa
    #
    wa
    #
    wa
    #
    vx
    wex
    @9
    @12
    vx
    wex
    wa
    @8
    @13
    vx
    @8
    @1
    @9
    @11
    wa
    #
    wa
    @13
    @7
    @14
    @1
    @7
    cA
    @10
    @10
    cxp
    #
    wcel
    @14
    @6
    @15
    cA
    @0
    cvv
    wcel
    @6
    @15
    wceq
    vx
    vex
    #
    vy
    @0
    @4
    @15
    cvv
    @5
    vy
    vx
    weq
    @3
    @10
    @2
    @0
    pweq
    sqxpeqd
    @5
    eqid
    @10
    @10
    @0
    @16
    pwex
    #
    @17
    xpex
    fvmpt
    ax-mp
    eleq2i
    cA
    @10
    @10
    elxp7
    bitri
    anbi2i
    @1
    @9
    @11
    an12
    bitri
    exbii
    @9
    @12
    vx
    19.42v
    bitri
end
