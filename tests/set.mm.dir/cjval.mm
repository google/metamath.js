include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmin.mm"
include "cmul.mm"
include "wa.mm"
include "cc.mm"
include "crio.mm"
include "ccj.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "df-cj.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem cjval
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. CC -> ( * ` A ) = ( iota_ x e. CC ( ( A + x ) e. RR /\ ( _i x. ( A - x ) ) e. RR ) ) )

  proof
    vy
    cA
    vy
    cv
    #
    vx
    cv
    #
    caddc
    co
    #
    cr
    wcel
    #
    ci
    @0
    @1
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    vx
    cc
    crio
    cA
    @1
    caddc
    co
    #
    cr
    wcel
    #
    ci
    cA
    @1
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    vx
    cc
    crio
    cc
    ccj
    @0
    cA
    wceq
    #
    @7
    @13
    vx
    cc
    @14
    @3
    @9
    @6
    @12
    @14
    @2
    @8
    cr
    @0
    cA
    @1
    caddc
    oveq1
    eleq1d
    @14
    @5
    @11
    cr
    @14
    @4
    @10
    ci
    cmul
    @0
    cA
    @1
    cmin
    oveq1
    oveq2d
    eleq1d
    anbi12d
    riotabidv
    vy
    vx
    df-cj
    @13
    vx
    cc
    riotaex
    fvmpt
end
