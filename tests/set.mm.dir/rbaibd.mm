include "wa.mm"
include "iba.mm"
include "bicomd.mm"
include "sylan9bb.mm"

theorem rbaibd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume baibd.1: |- ( ph -> ( ps <-> ( ch /\ th ) ) )


  assert |- ( ( ph /\ th ) -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    wth
    wa
    #
    wth
    wch
    baibd.1
    wth
    wch
    @0
    wth
    wch
    iba
    bicomd
    sylan9bb
end
