include "w3a.mm"
include "wa.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "syl222anc.mm"

theorem 3anandis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anandis.1: |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) ) -> ta )


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )

  proof
    wph
    wps
    wch
    wth
    w3a
    #
    wa
    wph
    wps
    wph
    wch
    wph
    wth
    wta
    wph
    @0
    simpl
    #
    wph
    wps
    wch
    wth
    simpr1
    @1
    wph
    wps
    wch
    wth
    simpr2
    @1
    wph
    wps
    wch
    wth
    simpr3
    3anandis.1
    syl222anc
end
