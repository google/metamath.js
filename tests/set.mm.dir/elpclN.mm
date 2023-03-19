include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "pclvalN.mm"
include "eleq2d.mm"
include "elintrab.mm"
include "syl6bb.mm"

theorem elpclN
  let vy: setvar y
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pclfval.a: |- A = ( Atoms ` K )
  assume pclfval.s: |- S = ( PSubSp ` K )
  assume pclfval.c: |- U = ( PCl ` K )
  assume elpcl.q: |- Q e. _V

  disjoint A y
  disjoint K y
  disjoint S y
  disjoint X y
  disjoint V y
  disjoint Q y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint K k
  disjoint K x
  disjoint S k
  disjoint S x
  disjoint X x
  disjoint p q
  disjoint p r
  disjoint A p
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint p y
  disjoint V p
  disjoint q y
  disjoint V q
  disjoint r y
  disjoint V r
  assert |- ( ( K e. V /\ X C_ A ) -> ( Q e. ( U ` X ) <-> A. y e. S ( X C_ y -> Q e. y ) ) )

  proof
    cK
    cV
    wcel
    cX
    cA
    wss
    wa
    #
    cQ
    cX
    cU
    cfv
    #
    wcel
    cQ
    cX
    vy
    cv
    #
    wss
    #
    vy
    cS
    crab
    cint
    #
    wcel
    @3
    cQ
    @2
    wcel
    wi
    vy
    cS
    wral
    @0
    @1
    @4
    cQ
    vy
    cA
    cS
    cU
    cK
    cV
    cX
    pclfval.a
    pclfval.s
    pclfval.c
    pclvalN
    eleq2d
    @3
    vy
    cQ
    cS
    elpcl.q
    elintrab
    syl6bb
end
