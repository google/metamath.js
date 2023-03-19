include "bicomi.mm"
include "sylnbi.mm"

theorem sylnbir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylnbir.1: |- ( ps <-> ph )
  assume sylnbir.2: |- ( -. ps -> ch )


  assert |- ( -. ph -> ch )

  proof
    wph
    wps
    wch
    wps
    wph
    sylnbir.1
    bicomi
    sylnbir.2
    sylnbi
end
