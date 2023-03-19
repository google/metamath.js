include "wcel.mm"
include "cab.mm"
include "cint.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "elintg.mm"
include "eleq2.mm"
include "ralab2.mm"
include "syl6bb.mm"

theorem elintabg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint ph y
  disjoint x y
  disjoint A y
  assert |- ( A e. V -> ( A e. |^| { x | ph } <-> A. x ( ph -> A e. x ) ) )

  proof
    cA
    cV
    wcel
    cA
    wph
    vx
    cab
    #
    cint
    wcel
    cA
    vy
    cv
    #
    wcel
    #
    vy
    @0
    wral
    wph
    cA
    vx
    cv
    #
    wcel
    #
    wi
    vx
    wal
    vy
    cA
    @0
    cV
    elintg
    wph
    @2
    @4
    vy
    vx
    @1
    @3
    cA
    eleq2
    ralab2
    syl6bb
end
