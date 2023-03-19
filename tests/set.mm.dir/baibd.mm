include "wa.mm"
include "ibar.mm"
include "bicomd.mm"
include "sylan9bb.mm"

theorem baibd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume baibd.1: |- ( ph -> ( ps <-> ( ch /\ th ) ) )


  assert |- ( ( ph /\ ch ) -> ( ps <-> th ) )

  proof
    wph
    wps
    wch
    wth
    wa
    #
    wch
    wth
    baibd.1
    wch
    wth
    @0
    wch
    wth
    ibar
    bicomd
    sylan9bb
end
