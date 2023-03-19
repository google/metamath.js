include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccom.mm"
include "cvv.mm"
include "adantr.mm"
include "cfv.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "elrabi.mm"
include "elmapi.mm"
include "eleq2s.mm"
include "adantl.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "wceq.mm"
include "jca.mm"
include "eqcomi.mm"
include "f1ocnvfv.mm"
include "imp.mm"
include "fsuppcor.mm"
include "wf1.mm"
include "f1of1.mm"
include "fex.mm"
include "cnvexg.mm"
include "coexg.mm"
include "sylan.mm"
include "fsuppco.mm"

theorem mapfienlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cW: class W
  let cZ: class Z
  let vf: setvar f
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
  disjoint g x
  disjoint F g
  disjoint F x
  disjoint G g
  disjoint G x
  disjoint g ph
  disjoint D x
  disjoint S g
  disjoint T g
  disjoint W x
  disjoint Z x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint G f
  disjoint f ph
  disjoint S f
  disjoint T f
  assert |- ( ( ph /\ g e. T ) -> ( ( `' G o. g ) o. `' F ) finSupp Z )

  proof
    wph
    vg
    cv
    #
    cT
    wcel
    #
    wa
    #
    cG
    ccnv
    #
    @0
    ccom
    #
    cF
    ccnv
    #
    cvv
    cB
    cA
    cC
    cZ
    @2
    cC
    cD
    cD
    cB
    cvv
    @0
    @3
    cvv
    cB
    cZ
    cW
    wph
    cZ
    cB
    wcel
    #
    @1
    mapfien.z
    adantr
    #
    wph
    cW
    cD
    wcel
    @1
    wph
    cW
    cZ
    cG
    cfv
    #
    cD
    mapfien.w
    wph
    cB
    cD
    cZ
    cG
    wph
    cB
    cD
    cG
    wf1o
    #
    cB
    cD
    cG
    wf
    #
    mapfien.g
    cB
    cD
    cG
    f1of
    syl
    #
    mapfien.z
    ffvelrnd
    syl5eqel
    adantr
    @1
    cC
    cD
    @0
    wf
    #
    wph
    @12
    @0
    vx
    cv
    #
    cW
    cfsupp
    wbr
    #
    vx
    cD
    cC
    cmap
    co
    #
    crab
    #
    cT
    @0
    @16
    wcel
    #
    @0
    @15
    wcel
    #
    @12
    @14
    vx
    @0
    @15
    elrabi
    @0
    cD
    cC
    elmapi
    syl
    mapfien.t
    eleq2s
    adantl
    wph
    cD
    cB
    @3
    wf
    #
    @1
    wph
    @9
    cD
    cB
    @3
    wf1o
    @19
    mapfien.g
    cB
    cD
    cG
    f1ocnv
    cD
    cB
    @3
    f1of
    3syl
    adantr
    cD
    cD
    wss
    @2
    cD
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
    cD
    cvv
    wcel
    @1
    mapfien.d
    adantr
    @1
    @0
    cW
    cfsupp
    wbr
    #
    wph
    @20
    @0
    @16
    cT
    @17
    @18
    @20
    @14
    @20
    vx
    @0
    @15
    @13
    @0
    cW
    cfsupp
    breq1
    elrab
    simprbi
    mapfien.t
    eleq2s
    adantl
    @2
    @9
    @6
    wa
    #
    @8
    cW
    wceq
    #
    wa
    #
    cW
    @3
    cfv
    cZ
    wceq
    #
    wph
    @23
    @1
    wph
    @21
    @22
    wph
    @9
    @6
    mapfien.g
    mapfien.z
    jca
    @22
    wph
    cW
    @8
    mapfien.w
    eqcomi
    a1i
    jca
    adantr
    @21
    @22
    @24
    cB
    cD
    cZ
    cW
    cG
    f1ocnvfv
    imp
    syl
    fsuppcor
    wph
    cA
    cC
    @5
    wf1
    #
    @1
    wph
    cC
    cA
    cF
    wf1o
    cA
    cC
    @5
    wf1o
    @25
    mapfien.f
    cC
    cA
    cF
    f1ocnv
    cA
    cC
    @5
    f1of1
    3syl
    adantr
    @7
    wph
    @3
    cvv
    wcel
    #
    @1
    @4
    cvv
    wcel
    wph
    @10
    cB
    cvv
    wcel
    #
    wa
    cG
    cvv
    wcel
    @26
    wph
    @10
    @27
    @11
    mapfien.b
    jca
    cB
    cD
    cvv
    cG
    fex
    cG
    cvv
    cnvexg
    3syl
    @3
    @0
    cvv
    cT
    coexg
    sylan
    fsuppco
end
