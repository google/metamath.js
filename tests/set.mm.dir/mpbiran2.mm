include "wa.mm"
include "biantru.mm"
include "bitr4i.mm"

theorem mpbiran2
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
