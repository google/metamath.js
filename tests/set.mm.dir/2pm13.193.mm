include "weq.mm"
include "wa.mm"
include "wsb.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "sbequ2.mm"
include "sylc.mm"
include "jca31.mm"
include "sbequ1.mm"
include "impbii.mm"

theorem 2pm13.193
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u


  assert |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) <-> ( ( x = u /\ y = v ) /\ ph ) )

  proof
    vx
    vu
    weq
    #
    vy
    vv
    weq
    #
    wa
    #
    wph
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    wa
    #
    @2
    wph
    wa
    #
    @5
    @0
    @1
    wph
    @0
    @1
    @4
    simpll
    #
    @0
    @1
    @4
    simplr
    #
    @5
    @1
    @3
    wph
    @8
    @5
    @0
    @4
    @3
    @7
    @2
    @4
    simpr
    @3
    vx
    vu
    sbequ2
    sylc
    wph
    vy
    vv
    sbequ2
    sylc
    jca31
    @6
    @0
    @1
    @4
    @0
    @1
    wph
    simpll
    #
    @0
    @1
    wph
    simplr
    #
    @6
    @0
    @3
    @4
    @9
    @6
    @1
    wph
    @3
    @10
    @2
    wph
    simpr
    wph
    vy
    vv
    sbequ1
    sylc
    @3
    vx
    vu
    sbequ1
    sylc
    jca31
    impbii
end
