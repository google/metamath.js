include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cv.mm"
include "cin.mm"
include "cfn.mm"
include "wdisj.mm"
include "cdif.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "issros.mm"
include "simp1bi.mm"
include "elpwid.mm"

theorem srossspw
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cS: class S
  let cN: class N
  let cO: class O
  let vs: setvar s
  let cA: class A
  let cB: class B
  assume issros.1: |- N = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x i^i y ) e. s /\ E. z e. ~P s ( z e. Fin /\ Disj_ t e. z t /\ ( x \ y ) = U. z ) ) ) }

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint O s
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint s z
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( S e. N -> S C_ ~P O )

  proof
    cS
    cN
    wcel
    #
    cS
    cO
    cpw
    #
    @0
    cS
    @1
    cpw
    wcel
    c0
    cS
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cin
    cS
    wcel
    vz
    cv
    #
    cfn
    wcel
    vt
    @4
    vt
    cv
    wdisj
    @2
    @3
    cdif
    @4
    cuni
    wceq
    w3a
    vz
    cS
    cpw
    wrex
    wa
    vy
    cS
    wral
    vx
    cS
    wral
    vx
    vy
    vz
    vt
    cS
    cN
    cO
    vs
    issros.1
    issros
    simp1bi
    elpwid
end
