include "a1i.mm"
include "mt4d.mm"

theorem mt4i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mt4i.1: |- ch
  assume mt4i.2: |- ( ph -> ( -. ps -> -. ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wch
    wps
    wch
    wph
    mt4i.1
    a1i
    mt4i.2
    mt4d
end
