include "w3a.mm"
include "wa.mm"
include "simpll1.mm"
include "simpll2.mm"
include "jca.mm"
include "simplr.mm"
include "simpr.mm"
include "syl21anc.mm"

theorem 3adantll3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3adantll3.1: |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ( ph /\ ps /\ et ) /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wet
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
    wps
    wet
    wch
    wth
    simpll1
    wph
    wps
    wet
    wch
    wth
    simpll2
    jca
    @0
    wch
    wth
    simplr
    @1
    wth
    simpr
    3adantll3.1
    syl21anc
end
