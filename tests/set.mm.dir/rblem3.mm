include "wo.mm"
include "wn.mm"
include "rb-ax2.mm"
include "rblem2.mm"
include "rbsyl.mm"

theorem rblem3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ( ch \/ ph ) \/ ( ( ch \/ ps ) \/ ph ) )

  proof
    wch
    wph
    wo
    wn
    #
    wph
    wch
    wps
    wo
    #
    wo
    #
    @1
    wph
    wo
    wph
    @1
    rb-ax2
    @0
    wph
    wch
    wo
    @2
    wch
    wps
    wph
    rblem2
    wch
    wph
    rb-ax2
    rbsyl
    rbsyl
end
