include "wn.mm"
include "notbii.mm"
include "sylbi.mm"

theorem sylnbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylnbi.1: |- ( ph <-> ps )
  assume sylnbi.2: |- ( -. ps -> ch )


  assert |- ( -. ph -> ch )

  proof
    wph
    wn
    wps
    wn
    wch
    wph
    wps
    sylnbi.1
    notbii
    sylnbi.2
    sylbi
end
