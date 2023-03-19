include "bicomi.mm"
include "sylnib.mm"

theorem sylnibr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylnibr.1: |- ( ph -> -. ps )
  assume sylnibr.2: |- ( ch <-> ps )


  assert |- ( ph -> -. ch )

  proof
    wph
    wps
    wch
    sylnibr.1
    wch
    wps
    sylnibr.2
    bicomi
    sylnib
end
