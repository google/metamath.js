include "w-bnj17.mm"
include "wa.mm"
include "w3a.mm"
include "bnj334.mm"
include "bnj250.mm"
include "3anass.mm"
include "bitr4i.mm"
include "3anrev.mm"
include "3bitri.mm"

theorem bnj345
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( th /\ ph /\ ps /\ ch ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wch
    wph
    wps
    wth
    w-bnj17
    #
    wch
    wph
    wps
    wa
    #
    wth
    w3a
    #
    wth
    wph
    wps
    wch
    w-bnj17
    #
    wph
    wps
    wch
    wth
    bnj334
    @0
    wch
    @1
    wth
    wa
    wa
    @2
    wch
    wph
    wps
    wth
    bnj250
    wch
    @1
    wth
    3anass
    bitr4i
    @2
    wth
    @1
    wch
    w3a
    #
    @3
    wch
    @1
    wth
    3anrev
    @3
    wth
    @1
    wch
    wa
    wa
    @4
    wth
    wph
    wps
    wch
    bnj250
    wth
    @1
    wch
    3anass
    bitr4i
    bitr4i
    3bitri
end
