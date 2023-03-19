include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "ci.mm"
include "cmin.mm"
include "cmul.mm"
include "wa.mm"
include "ccj.mm"
include "cfv.mm"
include "wsbc.mm"
include "crio.mm"
include "wreu.mm"
include "cju.mm"
include "riotasbc.mm"
include "syl.mm"
include "cjval.mm"
include "sbceq1d.mm"
include "mpbird.mm"
include "fvex.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq2d.mm"
include "anbi12d.mm"
include "sbcie.mm"
include "sylib.mm"

theorem cjth
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( ( A + ( * ` A ) ) e. RR /\ ( _i x. ( A - ( * ` A ) ) ) e. RR ) )

  proof
    cA
    cc
    wcel
    #
    cA
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
    cA
    ccj
    cfv
    #
    wsbc
    #
    cA
    @8
    caddc
    co
    #
    cr
    wcel
    #
    ci
    cA
    @8
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
    @0
    @9
    @7
    vx
    @7
    vx
    cc
    crio
    #
    wsbc
    #
    @0
    @7
    vx
    cc
    wreu
    @17
    vx
    cA
    cju
    @7
    vx
    cc
    riotasbc
    syl
    @0
    @7
    vx
    @8
    @16
    vx
    cA
    cjval
    sbceq1d
    mpbird
    @7
    @15
    vx
    @8
    cA
    ccj
    fvex
    @1
    @8
    wceq
    #
    @3
    @11
    @6
    @14
    @18
    @2
    @10
    cr
    @1
    @8
    cA
    caddc
    oveq2
    eleq1d
    @18
    @5
    @13
    cr
    @18
    @4
    @12
    ci
    cmul
    @1
    @8
    cA
    cmin
    oveq2
    oveq2d
    eleq1d
    anbi12d
    sbcie
    sylib
end
