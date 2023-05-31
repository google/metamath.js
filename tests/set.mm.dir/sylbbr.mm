include "biimpri.mm"
include "sylibr.mm"

theorem sylbbr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume sylbbr.1: |- ( ph <-> ps )
  assume sylbbr.2: |- ( ps <-> ch )


  assert |- ( ch -> ph )

  proof
    wch
    wps
    wph
    wps
    wch
    sylbbr.2
    biimpri
    sylbbr.1
    sylibr
end
