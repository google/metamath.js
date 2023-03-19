include "wn.mm"
include "wa.mm"
include "w3o.mm"
include "wi.mm"
include "wo.mm"
include "idn1.mm"
include "simpl.mm"
include "e1a.mm"
include "simpr.mm"
include "ioran.mm"
include "simplbi2.mm"
include "e11.mm"
include "idn2.mm"
include "3orass.mm"
include "biimpi.mm"
include "e2.mm"
include "orel2.mm"
include "e12.mm"
include "in2.mm"
include "in1.mm"

theorem 3ornot23VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( -. ph /\ -. ps ) -> ( ( ch \/ ph \/ ps ) -> ch ) )

  proof
    wph
    wn
    #
    wps
    wn
    #
    wa
    #
    wch
    wph
    wps
    w3o
    #
    wch
    wi
    @2
    @3
    wch
    @2
    wph
    wps
    wo
    #
    wn
    #
    @3
    wch
    @4
    wo
    #
    wch
    @2
    @0
    @1
    @5
    @2
    @2
    @0
    @2
    idn1
    #
    @0
    @1
    simpl
    e1a
    @2
    @2
    @1
    @7
    @0
    @1
    simpr
    e1a
    @5
    @0
    @1
    wph
    wps
    ioran
    simplbi2
    e11
    @2
    @3
    @3
    @6
    @2
    @3
    idn2
    @3
    @6
    wch
    wph
    wps
    3orass
    biimpi
    e2
    @4
    wch
    orel2
    e12
    in2
    in1
end
