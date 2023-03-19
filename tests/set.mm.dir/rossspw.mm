include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cv.mm"
include "cun.mm"
include "cdif.mm"
include "wa.mm"
include "wral.mm"
include "isros.mm"
include "simp1bi.mm"
include "elpwid.mm"

theorem rossspw
  let vx: setvar x
  let vy: setvar y
  let cQ: class Q
  let cS: class S
  let cO: class O
  let vs: setvar s
  let cA: class A
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  assume isros.1: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }

  disjoint O s
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint S u
  disjoint S v
  disjoint s u
  disjoint s v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( S e. Q -> S C_ ~P O )

  proof
    cS
    cQ
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
    vu
    cv
    #
    vv
    cv
    #
    cun
    cS
    wcel
    @2
    @3
    cdif
    cS
    wcel
    wa
    vv
    cS
    wral
    vu
    cS
    wral
    vx
    vy
    vv
    vu
    cQ
    cS
    cO
    vs
    isros.1
    isros
    simp1bi
    elpwid
end
