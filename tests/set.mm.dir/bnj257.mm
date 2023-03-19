include "wa.mm"
include "w-bnj17.mm"
include "ancom.mm"
include "anbi2i.mm"
include "bnj256.mm"
include "3bitr4i.mm"

theorem bnj257
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ps /\ th /\ ch ) )

  proof
    wph
    wps
    wa
    #
    wch
    wth
    wa
    #
    wa
    @0
    wth
    wch
    wa
    #
    wa
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wth
    wch
    w-bnj17
    @1
    @2
    @0
    wch
    wth
    ancom
    anbi2i
    wph
    wps
    wch
    wth
    bnj256
    wph
    wps
    wth
    wch
    bnj256
    3bitr4i
end
