include "wfun.mm"
include "cv.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cima.mm"
include "cuni.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "funimaex.mm"
include "adantr.mm"
include "wi.mm"
include "wceq.mm"
include "wrex.mm"
include "fvelima.mm"
include "ex.mm"
include "breq1.mm"
include "biimpd.mm"
include "reximi.mm"
include "r19.36v.mm"
include "syl.mm"
include "syl6.mm"
include "com23.mm"
include "imp.mm"
include "ralrimiv.mm"
include "unidom.mm"
include "syl2anc.mm"
include "imadomg.mm"
include "ax-mp.mm"
include "xpdom1.mm"
include "domtr.mm"

theorem uniimadom
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume uniimadom.1: |- A e. _V
  assume uniimadom.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  assert |- ( ( Fun F /\ A. x e. A ( F ` x ) ~<_ B ) -> U. ( F " A ) ~<_ ( A X. B ) )

  proof
    cF
    wfun
    #
    vx
    cv
    cF
    cfv
    #
    cB
    cdom
    wbr
    #
    vx
    cA
    wral
    #
    wa
    #
    cF
    cA
    cima
    #
    cuni
    #
    @5
    cB
    cxp
    #
    cdom
    wbr
    #
    @7
    cA
    cB
    cxp
    #
    cdom
    wbr
    #
    @6
    @9
    cdom
    wbr
    @4
    @5
    cvv
    wcel
    #
    vy
    cv
    #
    cB
    cdom
    wbr
    #
    vy
    @5
    wral
    @8
    @0
    @11
    @3
    cF
    cA
    uniimadom.1
    funimaex
    adantr
    @4
    @13
    vy
    @5
    @0
    @3
    @12
    @5
    wcel
    #
    @13
    wi
    @0
    @14
    @3
    @13
    @0
    @14
    @1
    @12
    wceq
    #
    vx
    cA
    wrex
    #
    @3
    @13
    wi
    #
    @0
    @14
    @16
    vx
    @12
    cA
    cF
    fvelima
    ex
    @16
    @2
    @13
    wi
    #
    vx
    cA
    wrex
    @17
    @15
    @18
    vx
    cA
    @15
    @2
    @13
    @1
    @12
    cB
    cdom
    breq1
    biimpd
    reximi
    @2
    @13
    vx
    cA
    r19.36v
    syl
    syl6
    com23
    imp
    ralrimiv
    vy
    @5
    cB
    cvv
    unidom
    syl2anc
    @0
    @10
    @3
    @0
    @5
    cA
    cdom
    wbr
    #
    @10
    cA
    cvv
    wcel
    @0
    @19
    wi
    uniimadom.1
    cA
    cvv
    cF
    imadomg
    ax-mp
    @5
    cA
    cB
    uniimadom.2
    xpdom1
    syl
    adantr
    @6
    @7
    @9
    domtr
    syl2anc
end
