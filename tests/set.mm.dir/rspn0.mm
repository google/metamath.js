include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wral.mm"
include "wi.mm"
include "n0.mm"
include "nfra1.mm"
include "nfv.mm"
include "nfim.mm"
include "rsp.mm"
include "com12.mm"
include "exlimi.mm"
include "sylbi.mm"

theorem rspn0
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  disjoint ph x
  assert |- ( A =/= (/) -> ( A. x e. A ph -> ph ) )

  proof
    cA
    c0
    wne
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    wph
    vx
    cA
    wral
    #
    wph
    wi
    #
    vx
    cA
    n0
    @0
    @2
    vx
    @1
    wph
    vx
    wph
    vx
    cA
    nfra1
    wph
    vx
    nfv
    nfim
    @1
    @0
    wph
    wph
    vx
    cA
    rsp
    com12
    exlimi
    sylbi
end
