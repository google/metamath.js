include "wa.mm"
include "simpr.mm"
include "simplr.mm"
include "jca.mm"
include "simpllr.mm"
include "simplll.mm"
include "syl21anc.mm"

theorem 4an4132
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 4an4132.1: |- ( ( ( ( th /\ ch ) /\ ps ) /\ ph ) -> ta )


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    #
    wth
    wa
    #
    wth
    wch
    wa
    wps
    wph
    wta
    @2
    wth
    wch
    @1
    wth
    simpr
    @0
    wch
    wth
    simplr
    jca
    wph
    wps
    wch
    wth
    simpllr
    wph
    wps
    wch
    wth
    simplll
    4an4132.1
    syl21anc
end
