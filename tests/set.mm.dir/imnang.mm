include "wn.mm"
include "wi.mm"
include "wa.mm"
include "imnan.mm"
include "albii.mm"

theorem imnang
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> -. ps ) <-> A. x -. ( ph /\ ps ) )

  proof
    wph
    wps
    wn
    wi
    wph
    wps
    wa
    wn
    vx
    wph
    wps
    imnan
    albii
end
