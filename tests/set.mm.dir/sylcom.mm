include "wi.mm"
include "a2i.mm"
include "syl.mm"

theorem sylcom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylcom.1: |- ( ph -> ( ps -> ch ) )
  assume sylcom.2: |- ( ps -> ( ch -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wth
    wi
    sylcom.1
    wps
    wch
    wth
    sylcom.2
    a2i
    syl
end
