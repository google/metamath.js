include "wn.mm"
include "wi.mm"
include "wa.mm"
include "imnan.mm"
include "mpbir.mm"

theorem imnani
  let wph: wff ph
  let wps: wff ps
  assume imnani.1: |- -. ( ph /\ ps )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wn
    wi
    wph
    wps
    wa
    wn
    imnani.1
    wph
    wps
    imnan
    mpbir
end
