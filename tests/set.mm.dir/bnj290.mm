include "w3a.mm"
include "wa.mm"
include "w-bnj17.mm"
include "3anrot.mm"
include "anbi2i.mm"
include "bnj252.mm"
include "3bitr4i.mm"

theorem bnj290
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ch /\ th /\ ps ) )

  proof
    wph
    wps
    wch
    wth
    w3a
    #
    wa
    wph
    wch
    wth
    wps
    w3a
    #
    wa
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wch
    wth
    wps
    w-bnj17
    @0
    @1
    wph
    wps
    wch
    wth
    3anrot
    anbi2i
    wph
    wps
    wch
    wth
    bnj252
    wph
    wch
    wth
    wps
    bnj252
    3bitr4i
end
