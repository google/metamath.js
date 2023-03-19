include "wral.mm"
include "wi.mm"
include "nfra1.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "rspa.mm"
include "ax-1.mm"
include "syl.mm"
include "ex.mm"
include "ralrimi.mm"

theorem ralimralim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ph -> A. x e. A ( ps -> ph ) )

  proof
    wph
    vx
    cA
    wral
    #
    wps
    wph
    wi
    #
    vx
    cA
    wph
    vx
    cA
    nfra1
    @0
    vx
    cv
    cA
    wcel
    #
    @1
    @0
    @2
    wa
    wph
    @1
    wph
    vx
    cA
    rspa
    wph
    wps
    ax-1
    syl
    ex
    ralrimi
end
