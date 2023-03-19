include "wo.mm"
include "wn.mm"
include "rb-ax1.mm"
include "anmp.mm"

theorem rbsyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume rbsyl.1: |- ( -. ps \/ ch )
  assume rbsyl.2: |- ( ph \/ ps )


  assert |- ( ph \/ ch )

  proof
    wph
    wps
    wo
    #
    wph
    wch
    wo
    #
    rbsyl.2
    wps
    wn
    wch
    wo
    @0
    wn
    @1
    wo
    rbsyl.1
    wph
    wps
    wch
    rb-ax1
    anmp
    anmp
end
