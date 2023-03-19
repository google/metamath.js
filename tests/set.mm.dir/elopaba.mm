include "copab.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "cxp.mm"
include "elopab.mm"
include "copsex2gb.mm"
include "bitri.mm"

theorem elopaba
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume copsex2ga.1: |- ( A = <. x , y >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  assert |- ( A e. { <. x , y >. | ps } <-> ( A e. ( _V X. _V ) /\ ph ) )

  proof
    cA
    wps
    vx
    vy
    copab
    wcel
    cA
    vx
    cv
    vy
    cv
    cop
    wceq
    wps
    wa
    vy
    wex
    vx
    wex
    cA
    cvv
    cvv
    cxp
    wcel
    wph
    wa
    wps
    vx
    vy
    cA
    elopab
    wph
    wps
    vx
    vy
    cA
    copsex2ga.1
    copsex2gb
    bitri
end
