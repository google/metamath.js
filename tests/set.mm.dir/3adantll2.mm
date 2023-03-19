include "w3a.mm"
include "wa.mm"
include "simpll1.mm"
include "simpll3.mm"
include "jca.mm"
include "simplr.mm"
include "simpr.mm"
include "syl21anc.mm"

theorem 3adantll2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3adantll2.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ( ph /\ et /\ ps ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wet
    wps
    w3a
    #
    wch
    wa
    #
    wth
    wa
    #
    wph
    wps
    wa
    wch
    wth
    wta
    @2
    wph
    wps
    wph
    wet
    wps
    wch
    wth
    simpll1
    wph
    wet
    wps
    wch
    wth
    simpll3
    jca
    @0
    wch
    wth
    simplr
    @1
    wth
    simpr
    3adantll2.1
    syl21anc
end
