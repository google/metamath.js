include "wi.mm"
include "wn.mm"
include "wo.mm"
include "rb-imdf.mm"
include "rblem6.mm"
include "anmp.mm"

theorem re1axmp
  let wph: wff ph
  let wps: wff ps
  assume re1axmp.min: |- ph
  assume re1axmp.maj: |- ( ph -> ps )


  assert |- ps

  proof
    wph
    wps
    re1axmp.min
    wph
    wps
    wi
    #
    wph
    wn
    wps
    wo
    #
    re1axmp.maj
    @0
    @1
    wph
    wps
    rb-imdf
    rblem6
    anmp
    anmp
end
