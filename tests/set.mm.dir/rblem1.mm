include "wo.mm"
include "wn.mm"
include "rb-ax1.mm"
include "anmp.mm"
include "rb-ax2.mm"
include "rbsyl.mm"

theorem rblem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume rblem1.1: |- ( -. ph \/ ps )
  assume rblem1.2: |- ( -. ch \/ th )


  assert |- ( -. ( ph \/ ch ) \/ ( ps \/ th ) )

  proof
    wph
    wch
    wo
    wn
    #
    wps
    wch
    wo
    #
    wps
    wth
    wo
    #
    wch
    wn
    wth
    wo
    @1
    wn
    @2
    wo
    rblem1.2
    wps
    wch
    wth
    rb-ax1
    anmp
    @0
    wch
    wps
    wo
    #
    @1
    wch
    wps
    rb-ax2
    @0
    wch
    wph
    wo
    #
    @3
    wph
    wn
    wps
    wo
    @4
    wn
    @3
    wo
    rblem1.1
    wch
    wph
    wps
    rb-ax1
    anmp
    wph
    wch
    rb-ax2
    rbsyl
    rbsyl
    rbsyl
end
