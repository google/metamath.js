include "wa.mm"
include "w3a.mm"
include "biantrur.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem triantru3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume triantru3.1: |- ph
  assume triantru3.2: |- ps


  assert |- ( ch <-> ( ph /\ ps /\ ch ) )

  proof
    wps
    wch
    wa
    #
    wph
    @0
    wa
    wch
    wph
    wps
    wch
    w3a
    wph
    @0
    triantru3.1
    biantrur
    wps
    wch
    triantru3.2
    biantrur
    wph
    wps
    wch
    3anass
    3bitr4i
end
