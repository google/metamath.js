include "wn.mm"
include "wo.mm"
include "rb-ax3.mm"
include "rblem5.mm"
include "anmp.mm"

theorem rblem7
  let wph: wff ph
  let wps: wff ps
  assume rblem7.1: |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) )


  assert |- ( -. ps \/ ph )

  proof
    wph
    wn
    wps
    wo
    wn
    #
    wps
    wn
    wph
    wo
    #
    wn
    #
    wo
    #
    wn
    #
    @1
    rblem7.1
    @2
    wn
    @3
    wo
    @4
    wn
    @1
    wo
    @2
    @0
    rb-ax3
    @1
    @3
    rblem5
    anmp
    anmp
end
