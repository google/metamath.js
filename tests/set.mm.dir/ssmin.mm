include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "ssintab.mm"
include "simpl.mm"
include "mpgbir.mm"

theorem ssmin
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph y
  assert |- A C_ |^| { x | ( A C_ x /\ ph ) }

  proof
    cA
    cA
    vx
    cv
    wss
    #
    wph
    wa
    #
    vx
    cab
    cint
    wss
    @1
    @0
    wi
    vx
    @1
    vx
    cA
    ssintab
    @0
    wph
    simpl
    mpgbir
end
