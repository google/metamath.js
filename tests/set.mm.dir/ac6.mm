include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "ciun.mm"
include "ccrd.mm"
include "cdm.mm"
include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "ssrab2.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "ssexi.mm"
include "numth3.mm"
include "ax-mp.mm"
include "ac6num.mm"
include "mp3an12.mm"

theorem ac6
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume ac6.1: |- A e. _V
  assume ac6.2: |- B e. _V
  assume ac6.3: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f ph
  disjoint ps y
  assert |- ( A. x e. A E. y e. B ph -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    cA
    cvv
    wcel
    vx
    cA
    wph
    vy
    cB
    crab
    #
    ciun
    #
    ccrd
    cdm
    wcel
    #
    wph
    vy
    cB
    wrex
    vx
    cA
    wral
    cA
    cB
    vf
    cv
    wf
    wps
    vx
    cA
    wral
    wa
    vf
    wex
    ac6.1
    @1
    cvv
    wcel
    @2
    @1
    cB
    ac6.2
    @1
    cB
    wss
    @0
    cB
    wss
    #
    vx
    cA
    wral
    @3
    vx
    cA
    wph
    vy
    cB
    ssrab2
    rgenw
    vx
    cA
    @0
    cB
    iunss
    mpbir
    ssexi
    @1
    cvv
    numth3
    ax-mp
    wph
    wps
    vx
    vy
    cA
    cB
    vf
    cvv
    ac6.3
    ac6num
    mp3an12
end
