include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "sprbisymrel.mm"
include "bren.mm"
include "sylibr.mm"

theorem sprsymrelen
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vp: setvar p
  let vc: setvar c
  let vf: setvar f
  let vk: setvar k
  assume sprsymrelf.p: |- P = ~P ( Pairs ` V )
  assume sprsymrelf.r: |- R = { r e. ~P ( V X. V ) | A. x e. V A. y e. V ( x r y <-> y r x ) }

  disjoint V x
  disjoint V y
  disjoint x y
  disjoint r x
  disjoint r y
  disjoint V r
  disjoint W x
  disjoint W y
  disjoint P p
  disjoint V c
  disjoint c x
  disjoint c y
  disjoint c p
  disjoint p x
  disjoint p y
  disjoint c r
  disjoint p r
  disjoint c f
  disjoint f p
  disjoint f x
  disjoint f y
  disjoint P f
  disjoint R f
  disjoint R p
  disjoint W c
  disjoint k x
  assert |- ( V e. W -> P ~~ R )

  proof
    cV
    cW
    wcel
    cP
    cR
    vf
    cv
    wf1o
    vf
    wex
    cP
    cR
    cen
    wbr
    vx
    vy
    cP
    cR
    vf
    cV
    cW
    vr
    sprsymrelf.p
    sprsymrelf.r
    sprbisymrel
    cP
    cR
    vf
    bren
    sylibr
end
