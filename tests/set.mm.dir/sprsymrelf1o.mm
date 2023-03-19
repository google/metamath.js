include "wcel.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "sprsymrelf1.mm"
include "a1i.mm"
include "sprsymrelfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem sprsymrelf1o
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vp: setvar p
  let vc: setvar c
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vq: setvar q
  let vt: setvar t
  let vk: setvar k
  assume sprsymrelf.p: |- P = ~P ( Pairs ` V )
  assume sprsymrelf.r: |- R = { r e. ~P ( V X. V ) | A. x e. V A. y e. V ( x r y <-> y r x ) }
  assume sprsymrelf.f: |- F = ( p e. P |-> { <. x , y >. | E. c e. p c = { x , y } } )

  disjoint c p
  disjoint c x
  disjoint c y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint p r
  disjoint R p
  disjoint V c
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint c r
  disjoint r x
  disjoint r y
  disjoint W c
  disjoint W x
  disjoint W y
  disjoint P p
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint c p
  disjoint p x
  disjoint p y
  disjoint X c
  disjoint X p
  disjoint X x
  disjoint X y
  disjoint a b
  disjoint a c
  disjoint a p
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b p
  disjoint b x
  disjoint b y
  disjoint F a
  disjoint F b
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint a f
  disjoint a q
  disjoint a t
  disjoint b f
  disjoint b q
  disjoint b t
  disjoint c f
  disjoint c q
  disjoint c t
  disjoint f q
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint t x
  disjoint t y
  disjoint r t
  disjoint F f
  disjoint F t
  disjoint P f
  disjoint P t
  disjoint R f
  disjoint f p
  disjoint R t
  disjoint V f
  disjoint V q
  disjoint V t
  disjoint W a
  disjoint W b
  disjoint W f
  disjoint W t
  disjoint k x
  assert |- ( V e. W -> F : P -1-1-onto-> R )

  proof
    cV
    cW
    wcel
    #
    cP
    cR
    cF
    wf1
    #
    cP
    cR
    cF
    wfo
    cP
    cR
    cF
    wf1o
    @1
    @0
    vx
    vy
    cP
    cR
    cF
    cV
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    sprsymrelf.f
    sprsymrelf1
    a1i
    vx
    vy
    cP
    cR
    cF
    cV
    cW
    vr
    vp
    vc
    sprsymrelf.p
    sprsymrelf.r
    sprsymrelf.f
    sprsymrelfo
    cP
    cR
    cF
    df-f1o
    sylanbrc
end
