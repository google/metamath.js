include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cfallfac.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cc.mm"
include "wceq.mm"
include "sseli.mm"
include "fallfacval.mm"
include "sylan.mm"
include "wss.mm"
include "a1i.mm"
include "cmul.mm"
include "adantl.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "sylan2.mm"
include "fprodcllem.mm"
include "adantr.mm"
include "eqeltrd.mm"

theorem fallfaccllem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cN: class N
  assume risefallfaccllem.1: |- S C_ CC
  assume risefallfaccllem.2: |- 1 e. S
  assume risefallfaccllem.3: |- ( ( x e. S /\ y e. S ) -> ( x x. y ) e. S )
  assume fallfaccllem.4: |- ( ( A e. S /\ k e. NN0 ) -> ( A - k ) e. S )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint x y
  assert |- ( ( A e. S /\ N e. NN0 ) -> ( A FallFac N ) e. S )

  proof
    cA
    cS
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    cA
    cN
    cfallfac
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    cv
    #
    cmin
    co
    #
    vk
    cprod
    #
    cS
    @0
    cA
    cc
    wcel
    @1
    @2
    @7
    wceq
    cS
    cc
    cA
    risefallfaccllem.1
    sseli
    cA
    vk
    cN
    fallfacval
    sylan
    @0
    @7
    cS
    wcel
    @1
    @0
    vx
    vy
    @4
    @6
    cS
    vk
    cS
    cc
    wss
    @0
    risefallfaccllem.1
    a1i
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    @8
    @9
    cmul
    co
    cS
    wcel
    @0
    risefallfaccllem.3
    adantl
    @0
    cc0
    @3
    fzfid
    @5
    @4
    wcel
    @0
    @5
    cn0
    wcel
    @6
    cS
    wcel
    @5
    @3
    elfznn0
    fallfaccllem.4
    sylan2
    c1
    cS
    wcel
    @0
    risefallfaccllem.2
    a1i
    fprodcllem
    adantr
    eqeltrd
end
