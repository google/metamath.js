include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cixp.mm"
include "wa.mm"
include "cuni.mm"
include "ciun.mm"
include "cxp.mm"
include "wss.mm"
include "uniixp.mm"
include "iunexg.mm"
include "xpexg.mm"
include "syldan.mm"
include "ssexg.mm"
include "sylancr.mm"
include "uniexb.mm"
include "sylibr.mm"
include "wn.mm"
include "c0.mm"
include "ixpprc.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem ixpexg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let cF: class F
  let cC: class C

  disjoint A x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint F x
  disjoint C f
  assert |- ( A. x e. A B e. V -> X_ x e. A B e. _V )

  proof
    cA
    cvv
    wcel
    #
    cB
    cV
    wcel
    vx
    cA
    wral
    #
    vx
    cA
    cB
    cixp
    #
    cvv
    wcel
    #
    @0
    @1
    wa
    #
    @2
    cuni
    #
    cvv
    wcel
    #
    @3
    @4
    @5
    cA
    vx
    cA
    cB
    ciun
    #
    cxp
    #
    wss
    @8
    cvv
    wcel
    #
    @6
    vx
    cA
    cB
    uniixp
    @0
    @1
    @7
    cvv
    wcel
    @9
    vx
    cA
    cB
    cvv
    cV
    iunexg
    cA
    @7
    cvv
    cvv
    xpexg
    syldan
    @5
    @8
    cvv
    ssexg
    sylancr
    @2
    uniexb
    sylibr
    @0
    wn
    #
    @3
    @1
    @10
    @2
    c0
    cvv
    vx
    cA
    cB
    ixpprc
    0ex
    syl6eqel
    adantr
    pm2.61ian
end
