include "ctsr.mm"
include "wcel.mm"
include "cps.mm"
include "cxp.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wral.mm"
include "istsr.mm"
include "qfto.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem istsr2
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cX: class X
  let cA: class A
  let cB: class B
  let vr: setvar r
  assume istsr.1: |- X = dom R

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint X r
  assert |- ( R e. TosetRel <-> ( R e. PosetRel /\ A. x e. X A. y e. X ( x R y \/ y R x ) ) )

  proof
    cR
    ctsr
    wcel
    cR
    cps
    wcel
    #
    cX
    cX
    cxp
    cR
    cR
    ccnv
    cun
    wss
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @3
    @2
    cR
    wbr
    wo
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    cR
    cX
    istsr.1
    istsr
    @1
    @4
    @0
    vx
    vy
    cX
    cX
    cR
    qfto
    anbi2i
    bitri
end
