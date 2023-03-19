include "wn.mm"
include "wi.mm"
include "wa.mm"
include "imnan.mm"
include "albii.mm"

theorem imnang
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


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
