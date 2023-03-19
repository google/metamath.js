include "wn.mm"
include "wo.mm"
include "rb-ax4.mm"
include "rb-ax3.mm"
include "rbsyl.mm"
include "rb-ax2.mm"
include "anmp.mm"
include "rblem3.mm"
include "rblem5.mm"

theorem rblem6
  let wph: wff ph
  let wps: wff ps
  assume rblem6.1: |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) )


  assert |- ( -. ph \/ ps )

  proof
    wph
    wn
    wps
    wo
    #
    wn
    #
    wps
    wn
    wph
    wo
    wn
    #
    wo
    #
    wn
    #
    @0
    rblem6.1
    @1
    wn
    #
    @3
    wo
    #
    @4
    wn
    @0
    wo
    @3
    @5
    wo
    #
    @6
    @1
    @5
    wo
    #
    @7
    @5
    @1
    wo
    @8
    @5
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
    @5
    @1
    rb-ax2
    anmp
    @5
    @2
    @1
    rblem3
    anmp
    @3
    @5
    rb-ax2
    anmp
    @0
    @3
    rblem5
    anmp
    anmp
end
