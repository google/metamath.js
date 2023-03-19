include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "cxp.mm"
include "cpw.mm"
include "cmpt.mm"
include "a1i.mm"
include "rexeq.mm"
include "opabbidv.mm"
include "adantl.mm"
include "id.mm"
include "cspr.mm"
include "cfv.mm"
include "wss.mm"
include "elpwi.mm"
include "eleq2s.mm"
include "sprsymrelfvlem.mm"
include "syl.mm"
include "fvmptd.mm"

theorem sprsymrelfv
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cF: class F
  let cV: class V
  let cX: class X
  let vr: setvar r
  let vp: setvar p
  let vc: setvar c
  let vk: setvar k
  assume sprsymrelf.p: |- P = ~P ( Pairs ` V )
  assume sprsymrelf.r: |- R = { r e. ~P ( V X. V ) | A. x e. V A. y e. V ( x r y <-> y r x ) }
  assume sprsymrelf.f: |- F = ( p e. P |-> { <. x , y >. | E. c e. p c = { x , y } } )

  disjoint X c
  disjoint X p
  disjoint X x
  disjoint X y
  disjoint c p
  disjoint c x
  disjoint c y
  disjoint p x
  disjoint p y
  disjoint x y
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
  disjoint k x
  assert |- ( X e. P -> ( F ` X ) = { <. x , y >. | E. c e. X c = { x , y } } )

  proof
    cX
    cP
    wcel
    #
    vp
    cX
    vc
    cv
    vx
    cv
    vy
    cv
    cpr
    wceq
    #
    vc
    vp
    cv
    #
    wrex
    #
    vx
    vy
    copab
    #
    @1
    vc
    cX
    wrex
    #
    vx
    vy
    copab
    #
    cP
    cF
    cV
    cV
    cxp
    cpw
    #
    cF
    vp
    cP
    @4
    cmpt
    wceq
    @0
    sprsymrelf.f
    a1i
    @2
    cX
    wceq
    #
    @4
    @6
    wceq
    @0
    @8
    @3
    @5
    vx
    vy
    @1
    vc
    @2
    cX
    rexeq
    opabbidv
    adantl
    @0
    id
    @0
    cX
    cV
    cspr
    cfv
    #
    wss
    #
    @6
    @7
    wcel
    @10
    cX
    @9
    cpw
    cP
    cX
    @9
    elpwi
    sprsymrelf.p
    eleq2s
    vx
    vy
    cX
    cV
    vc
    sprsymrelfvlem
    syl
    fvmptd
end
