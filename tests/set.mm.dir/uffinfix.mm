include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cint.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "cpw.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "cfil.mm"
include "ufilfil.mm"
include "filfinnfr.mm"
include "syl3an1.mm"
include "wb.mm"
include "uffix2.mm"
include "3ad2ant1.mm"
include "mpbid.mm"

theorem uffinfix
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cX: class X
  let cA: class A

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint A x
  assert |- ( ( F e. ( UFil ` X ) /\ S e. F /\ S e. Fin ) -> E. x e. X F = { y e. ~P X | x e. y } )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cS
    cF
    wcel
    #
    cS
    cfn
    wcel
    #
    w3a
    cF
    cint
    c0
    wne
    #
    cF
    vx
    vy
    wel
    vy
    cX
    cpw
    crab
    wceq
    vx
    cX
    wrex
    #
    @0
    cF
    cX
    cfil
    cfv
    wcel
    @1
    @2
    @3
    cF
    cX
    ufilfil
    cS
    cF
    cX
    filfinnfr
    syl3an1
    @0
    @1
    @3
    @4
    wb
    @2
    vx
    vy
    cF
    cX
    uffix2
    3ad2ant1
    mpbid
end
