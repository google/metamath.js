include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wsb.mm"
include "idn1.mm"
include "simpl.mm"
include "e1a.mm"
include "simpr.mm"
include "pm3.21.mm"
include "e11.mm"
include "sbequ2.mm"
include "imdistanri.mm"
include "pm3.2.mm"
include "in1.mm"
include "sbequ1.mm"
include "impbii.mm"

theorem 2pm13.193VD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u


  assert |- ( ( ( x = u /\ y = v ) /\ [ u / x ] [ v / y ] ph ) <-> ( ( x = u /\ y = v ) /\ ph ) )

  proof
    vx
    cv
    vu
    cv
    wceq
    #
    vy
    cv
    vv
    cv
    wceq
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
    @6
    @5
    @2
    wph
    @6
    @5
    @5
    @2
    @5
    idn1
    #
    @2
    @4
    simpl
    e1a
    #
    @5
    wph
    @1
    wa
    #
    wph
    @5
    @3
    @1
    wa
    #
    @9
    @5
    @3
    @1
    @10
    @5
    @3
    @0
    wa
    #
    @3
    @5
    @4
    @0
    wa
    #
    @11
    @5
    @0
    @4
    @12
    @5
    @2
    @0
    @8
    @0
    @1
    simpl
    #
    e1a
    @5
    @5
    @4
    @7
    @2
    @4
    simpr
    e1a
    @0
    @4
    pm3.21
    e11
    @0
    @4
    @3
    @3
    vx
    vu
    sbequ2
    imdistanri
    e1a
    @3
    @0
    simpl
    e1a
    @5
    @2
    @1
    @8
    @0
    @1
    simpr
    #
    e1a
    @3
    @1
    pm3.2
    e11
    @1
    @3
    wph
    wph
    vy
    vv
    sbequ2
    imdistanri
    e1a
    wph
    @1
    simpl
    e1a
    @2
    wph
    pm3.2
    e11
    in1
    @6
    @5
    @6
    @2
    @4
    @5
    @6
    @6
    @2
    @6
    idn1
    #
    @2
    wph
    simpl
    e1a
    #
    @6
    @12
    @4
    @6
    @11
    @12
    @6
    @0
    @3
    @11
    @6
    @2
    @0
    @16
    @13
    e1a
    @6
    @10
    @3
    @6
    @9
    @10
    @6
    @1
    wph
    @9
    @6
    @2
    @1
    @16
    @14
    e1a
    @6
    @6
    wph
    @15
    @2
    wph
    simpr
    e1a
    @1
    wph
    pm3.21
    e11
    @1
    wph
    @3
    wph
    vy
    vv
    sbequ1
    imdistanri
    e1a
    @3
    @1
    simpl
    e1a
    @0
    @3
    pm3.21
    e11
    @0
    @3
    @4
    @3
    vx
    vu
    sbequ1
    imdistanri
    e1a
    @4
    @0
    simpl
    e1a
    @2
    @4
    pm3.2
    e11
    in1
    impbii
end
