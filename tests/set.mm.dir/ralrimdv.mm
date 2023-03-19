include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "imp.mm"
include "ralrimiv.mm"
include "ex.mm"

theorem ralrimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralrimdv.1: |- ( ph -> ( ps -> ( x e. A -> ch ) ) )

  disjoint ph x
  disjoint ps x
  assert |- ( ph -> ( ps -> A. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wral
    wph
    wps
    wa
    wch
    vx
    cA
    wph
    wps
    vx
    cv
    cA
    wcel
    wch
    wi
    ralrimdv.1
    imp
    ralrimiv
    ex
end
