include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "ccom.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "adantr.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "elrabi.mm"
include "elmapi.mm"
include "syl.mm"
include "eleq2s.mm"
include "wf1o.mm"
include "f1of.mm"
include "fco.mm"
include "syl2anr.mm"
include "wss.mm"
include "ssid.mm"
include "breq1.mm"
include "elrab2.mm"
include "simprbi.mm"
include "adantl.mm"
include "wf1.mm"
include "f1of1.mm"
include "simpr.mm"
include "fsuppco.mm"
include "wceq.mm"
include "eqcomi.mm"
include "fsuppcor.mm"

theorem mapfienlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cW: class W
  let cZ: class Z
  let vg: setvar g
  assume mapfien.s: |- S = { x e. ( B ^m A ) | x finSupp Z }
  assume mapfien.t: |- T = { x e. ( D ^m C ) | x finSupp W }
  assume mapfien.w: |- W = ( G ` Z )
  assume mapfien.f: |- ( ph -> F : C -1-1-onto-> A )
  assume mapfien.g: |- ( ph -> G : B -1-1-onto-> D )
  assume mapfien.a: |- ( ph -> A e. _V )
  assume mapfien.b: |- ( ph -> B e. _V )
  assume mapfien.c: |- ( ph -> C e. _V )
  assume mapfien.d: |- ( ph -> D e. _V )
  assume mapfien.z: |- ( ph -> Z e. B )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint f x
  disjoint F f
  disjoint F x
  disjoint G f
  disjoint G x
  disjoint f ph
  disjoint D x
  disjoint S f
  disjoint T f
  disjoint W x
  disjoint Z x
  disjoint f g
  disjoint g x
  disjoint F g
  disjoint G g
  disjoint g ph
  disjoint S g
  disjoint T g
  assert |- ( ( ph /\ f e. S ) -> ( G o. ( f o. F ) ) finSupp W )

  proof
    wph
    vf
    cv
    #
    cS
    wcel
    #
    wa
    #
    cC
    cB
    cB
    cD
    cvv
    @0
    cF
    ccom
    #
    cG
    cvv
    cvv
    cW
    cZ
    cW
    cvv
    wcel
    @2
    cW
    cZ
    cG
    cfv
    #
    cvv
    mapfien.w
    cZ
    cG
    fvex
    eqeltri
    a1i
    wph
    cZ
    cB
    wcel
    @1
    mapfien.z
    adantr
    #
    @1
    cA
    cB
    @0
    wf
    #
    cC
    cA
    cF
    wf
    #
    cC
    cB
    @3
    wf
    wph
    @6
    @0
    vx
    cv
    #
    cZ
    cfsupp
    wbr
    #
    vx
    cB
    cA
    cmap
    co
    #
    crab
    #
    cS
    @0
    @11
    wcel
    @0
    @10
    wcel
    #
    @6
    @9
    vx
    @0
    @10
    elrabi
    @0
    cB
    cA
    elmapi
    syl
    mapfien.s
    eleq2s
    wph
    cC
    cA
    cF
    wf1o
    #
    @7
    mapfien.f
    cC
    cA
    cF
    f1of
    syl
    cC
    cA
    cB
    @0
    cF
    fco
    syl2anr
    wph
    cB
    cD
    cG
    wf
    #
    @1
    wph
    cB
    cD
    cG
    wf1o
    @14
    mapfien.g
    cB
    cD
    cG
    f1of
    syl
    adantr
    cB
    cB
    wss
    @2
    cB
    ssid
    a1i
    wph
    cC
    cvv
    wcel
    @1
    mapfien.c
    adantr
    wph
    cB
    cvv
    wcel
    @1
    mapfien.b
    adantr
    @2
    @0
    cF
    cS
    cB
    cC
    cA
    cZ
    @1
    @0
    cZ
    cfsupp
    wbr
    #
    wph
    @1
    @12
    @15
    @9
    @15
    vx
    @0
    @10
    cS
    @8
    @0
    cZ
    cfsupp
    breq1
    mapfien.s
    elrab2
    simprbi
    adantl
    wph
    cC
    cA
    cF
    wf1
    #
    @1
    wph
    @13
    @16
    mapfien.f
    cC
    cA
    cF
    f1of1
    syl
    adantr
    @5
    wph
    @1
    simpr
    fsuppco
    @4
    cW
    wceq
    @2
    cW
    @4
    mapfien.w
    eqcomi
    a1i
    fsuppcor
end
