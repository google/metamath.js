include "w3a.mm"
include "wa.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "jca.mm"
include "simpr.mm"
include "syl21anc.mm"

theorem 3adantlr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3adantlr3.1: |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ( ps /\ ch /\ et ) ) /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wet
    w3a
    #
    wa
    #
    wth
    wa
    #
    wph
    wps
    wch
    wa
    wth
    wta
    wph
    @0
    wth
    simpll
    @2
    wps
    wch
    wps
    wch
    wet
    wph
    wth
    simplr1
    wps
    wch
    wet
    wph
    wth
    simplr2
    jca
    @1
    wth
    simpr
    3adantlr3.1
    syl21anc
end
