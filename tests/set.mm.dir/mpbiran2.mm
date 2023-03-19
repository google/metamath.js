include "wa.mm"
include "biantru.mm"
include "bitr4i.mm"

theorem mpbiran2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpbiran2.1: |- ch
  assume mpbiran2.2: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ph <-> ps )

  proof
    wph
    wps
    wch
    wa
    wps
    mpbiran2.2
    wch
    wps
    mpbiran2.1
    biantru
    bitr4i
end
