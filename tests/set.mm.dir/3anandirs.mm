include "w3a.mm"
include "wa.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "syl222anc.mm"

theorem 3anandirs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anandirs.1: |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) ) -> ta )


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    wph
    wth
    wps
    wth
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    simpl1
    @0
    wth
    simpr
    #
    wph
    wps
    wch
    wth
    simpl2
    @1
    wph
    wps
    wch
    wth
    simpl3
    @1
    3anandirs.1
    syl222anc
end
