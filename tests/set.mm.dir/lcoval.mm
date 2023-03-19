include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "lcoop.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem lcoval
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vm: setvar m
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume lcoop.b: |- B = ( Base ` M )
  assume lcoop.s: |- S = ( Scalar ` M )
  assume lcoop.r: |- R = ( Base ` S )

  disjoint M s
  disjoint R s
  disjoint V s
  disjoint C s
  disjoint B c
  disjoint B m
  disjoint B v
  disjoint c m
  disjoint c v
  disjoint m v
  disjoint M c
  disjoint M m
  disjoint M v
  disjoint c s
  disjoint m s
  disjoint s v
  disjoint R c
  disjoint R m
  disjoint R v
  disjoint S m
  disjoint S v
  disjoint V c
  disjoint V m
  disjoint V v
  disjoint C c
  disjoint S c
  disjoint k x
  assert |- ( ( M e. X /\ V e. ~P B ) -> ( C e. ( M LinCo V ) <-> ( C e. B /\ E. s e. ( R ^m V ) ( s finSupp ( 0g ` S ) /\ C = ( s ( linC ` M ) V ) ) ) ) )

  proof
    cM
    cX
    wcel
    cV
    cB
    cpw
    wcel
    wa
    #
    cC
    cM
    cV
    clinco
    co
    #
    wcel
    cC
    vs
    cv
    #
    cS
    c0g
    cfv
    cfsupp
    wbr
    #
    vc
    cv
    #
    @2
    cV
    cM
    clinc
    cfv
    co
    #
    wceq
    #
    wa
    #
    vs
    cR
    cV
    cmap
    co
    #
    wrex
    #
    vc
    cB
    crab
    #
    wcel
    cC
    cB
    wcel
    @3
    cC
    @5
    wceq
    #
    wa
    #
    vs
    @8
    wrex
    #
    wa
    @0
    @1
    @10
    cC
    cB
    cR
    cS
    cM
    cV
    cX
    vs
    vc
    lcoop.b
    lcoop.s
    lcoop.r
    lcoop
    eleq2d
    @9
    @13
    vc
    cC
    cB
    @4
    cC
    wceq
    #
    @7
    @12
    vs
    @8
    @14
    @6
    @11
    @3
    @4
    cC
    @5
    eqeq1
    anbi2d
    rexbidv
    elrab
    syl6bb
end
