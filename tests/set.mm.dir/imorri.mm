include "wi.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "mpbir.mm"

theorem imorri
  let wph: wff ph
  let wps: wff ps
  assume imorri.1: |- ( -. ph \/ ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wi
    wph
    wn
    wps
    wo
    imorri.1
    wph
    wps
    imor
    mpbir
end
