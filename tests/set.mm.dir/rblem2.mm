include "wn.mm"
include "wo.mm"
include "rb-ax2.mm"
include "rb-ax3.mm"
include "rbsyl.mm"
include "rb-ax1.mm"
include "anmp.mm"

theorem rblem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ( ch \/ ph ) \/ ( ch \/ ( ph \/ ps ) ) )

  proof
    wph
    wn
    #
    wph
    wps
    wo
    #
    wo
    wch
    wph
    wo
    wn
    wch
    @1
    wo
    wo
    @0
    wps
    wph
    wo
    @1
    wps
    wph
    rb-ax2
    wph
    wps
    rb-ax3
    rbsyl
    wch
    wph
    @1
    rb-ax1
    anmp
end
