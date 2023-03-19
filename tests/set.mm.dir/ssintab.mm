include "cab.mm"
include "cint.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "ssint.mm"
include "sseq2.mm"
include "ralab2.mm"
include "bitri.mm"

theorem ssintab
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
  assert |- ( A C_ |^| { x | ph } <-> A. x ( ph -> A C_ x ) )

  proof
    cA
    wph
    vx
    cab
    #
    cint
    wss
    cA
    vy
    cv
    #
    wss
    #
    vy
    @0
    wral
    wph
    cA
    vx
    cv
    #
    wss
    #
    wi
    vx
    wal
    vy
    cA
    @0
    ssint
    wph
    @2
    @4
    vy
    vx
    @1
    @3
    cA
    sseq2
    ralab2
    bitri
end
