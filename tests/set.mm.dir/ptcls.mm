include "ciun.mm"
include "cvv.mm"
include "wacn.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wa.mm"
include "ctopon.mm"
include "cfv.mm"
include "toponmax.mm"
include "syl.mm"
include "ssexd.mm"
include "ralrimiva.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "wac.mm"
include "wceq.mm"
include "axac3.mm"
include "acacni.mm"
include "sylancr.mm"
include "eleqtrrd.mm"
include "ptclsg.mm"

theorem ptcls
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let vk: setvar k
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vh: setvar h
  assume ptcls.2: |- J = ( Xt_ ` ( k e. A |-> R ) )
  assume ptcls.a: |- ( ph -> A e. V )
  assume ptcls.j: |- ( ( ph /\ k e. A ) -> R e. ( TopOn ` X ) )
  assume ptcls.c: |- ( ( ph /\ k e. A ) -> S C_ X )

  disjoint k ph
  disjoint A k
  disjoint f g
  disjoint f k
  disjoint f u
  disjoint f ph
  disjoint g k
  disjoint g u
  disjoint g ph
  disjoint k u
  disjoint ph u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint f h
  disjoint S f
  disjoint g h
  disjoint S g
  disjoint h u
  disjoint h y
  disjoint h z
  disjoint S h
  disjoint S u
  disjoint S y
  disjoint S z
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint A f
  disjoint A g
  disjoint h k
  disjoint h x
  disjoint A h
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint J f
  assert |- ( ph -> ( ( cls ` J ) ` X_ k e. A S ) = X_ k e. A ( ( cls ` R ) ` S ) )

  proof
    wph
    cA
    cR
    cS
    vk
    cJ
    cV
    cX
    ptcls.2
    ptcls.a
    ptcls.j
    ptcls.c
    wph
    vk
    cA
    cS
    ciun
    #
    cvv
    cA
    wacn
    #
    wph
    cA
    cV
    wcel
    #
    cS
    cvv
    wcel
    #
    vk
    cA
    wral
    @0
    cvv
    wcel
    ptcls.a
    wph
    @3
    vk
    cA
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cS
    cX
    cR
    @4
    cR
    cX
    ctopon
    cfv
    wcel
    cX
    cR
    wcel
    ptcls.j
    cX
    cR
    toponmax
    syl
    ptcls.c
    ssexd
    ralrimiva
    vk
    cA
    cS
    cV
    cvv
    iunexg
    syl2anc
    wph
    wac
    @2
    @1
    cvv
    wceq
    axac3
    ptcls.a
    cA
    cV
    acacni
    sylancr
    eleqtrrd
    ptclsg
end
