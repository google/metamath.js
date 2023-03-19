include "wn.mm"
include "wo.mm"
include "rb-ax2.mm"
include "rb-ax4.mm"
include "rb-ax3.mm"
include "rbsyl.mm"
include "anmp.mm"
include "rblem1.mm"

theorem rblem5
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( -. -. ph \/ ps ) \/ ( -. -. ps \/ ph ) )

  proof
    wph
    wn
    #
    wn
    #
    wps
    wo
    wn
    wph
    wps
    wn
    #
    wn
    #
    wo
    @3
    wph
    wo
    wph
    @3
    rb-ax2
    @1
    wph
    wps
    @3
    @0
    wph
    wo
    @1
    wn
    #
    wph
    wo
    @0
    wph
    wph
    wo
    wph
    wph
    rb-ax4
    wph
    wph
    rb-ax3
    rbsyl
    #
    @0
    @4
    wph
    wph
    @4
    @1
    wo
    @1
    @4
    wo
    @4
    @1
    @1
    wo
    @1
    @1
    rb-ax4
    @1
    @1
    rb-ax3
    rbsyl
    @4
    @1
    rb-ax2
    anmp
    @5
    rblem1
    anmp
    @3
    @2
    wo
    @2
    @3
    wo
    @3
    @2
    @2
    wo
    @2
    @2
    rb-ax4
    @2
    @2
    rb-ax3
    rbsyl
    @3
    @2
    rb-ax2
    anmp
    rblem1
    rbsyl
end
