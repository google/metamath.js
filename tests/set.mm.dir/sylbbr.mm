include "biimpri.mm"
include "sylibr.mm"

theorem sylbbr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
