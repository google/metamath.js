include "wa.mm"
include "simpl.mm"
include "nsyl.mm"

theorem intnanrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume intnand.1: |- ( ph -> -. ps )


  assert |- ( ph -> -. ( ps /\ ch ) )

  proof
    wph
    wps
    wps
    wch
    wa
    intnand.1
    wps
    wch
    simpl
    nsyl
end
