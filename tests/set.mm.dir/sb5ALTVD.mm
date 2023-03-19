include "wsb.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wb.mm"
include "idn1.mm"
include "equsb1.mm"
include "sban.mm"
include "simplbi2com.mm"
include "e10.mm"
include "spsbe.mm"
include "e1a.mm"
include "in1.mm"
include "hbs1.mm"
include "idn2.mm"
include "simpr.mm"
include "e2.mm"
include "simpl.mm"
include "sbequ1.mm"
include "com12.mm"
include "e22.mm"
include "exinst.mm"
include "pm3.2i.mm"
include "impbi.mm"
include "imp.mm"
include "e0a.mm"

theorem sb5ALTVD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    cv
    vy
    cv
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    wi
    #
    @3
    @0
    wi
    #
    wa
    @0
    @3
    wb
    #
    @4
    @5
    @0
    @3
    @0
    @2
    vx
    vy
    wsb
    #
    @3
    @0
    @0
    @1
    vx
    vy
    wsb
    #
    @7
    @0
    idn1
    vx
    vy
    equsb1
    @7
    @8
    @0
    @1
    wph
    vx
    vy
    sban
    simplbi2com
    e10
    @2
    vx
    vy
    spsbe
    e1a
    in1
    @2
    @0
    vx
    wph
    vx
    vy
    hbs1
    @3
    @2
    wph
    @1
    @0
    @3
    @2
    @2
    wph
    @3
    @2
    idn2
    #
    @1
    wph
    simpr
    e2
    @3
    @2
    @2
    @1
    @9
    @1
    wph
    simpl
    e2
    @1
    wph
    @0
    wph
    vx
    vy
    sbequ1
    com12
    e22
    exinst
    pm3.2i
    @4
    @5
    @6
    @0
    @3
    impbi
    imp
    e0a
end
