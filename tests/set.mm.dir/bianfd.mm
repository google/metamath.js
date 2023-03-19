include "wa.mm"
include "intnanrd.mm"
include "2falsed.mm"

theorem bianfd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bianfd.1: |- ( ph -> -. ps )


  assert |- ( ph -> ( ps <-> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wps
    wch
    wa
    bianfd.1
    wph
    wps
    wch
    bianfd.1
    intnanrd
    2falsed
end
