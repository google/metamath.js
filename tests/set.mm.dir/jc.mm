include "wn.mm"
include "wi.mm"
include "pm3.2im.mm"
include "sylc.mm"

theorem jc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jc.1: |- ( ph -> ps )
  assume jc.2: |- ( ph -> ch )


  assert |- ( ph -> -. ( ps -> -. ch ) )

  proof
    wph
    wps
    wch
    wps
    wch
    wn
    wi
    wn
    jc.1
    jc.2
    wps
    wch
    pm3.2im
    sylc
end
