include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccom.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wf.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "adantr.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "adantl.mm"
include "elmapi.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "wb.mm"
include "cvv.mm"
include "elmapd.mm"
include "mpbird.mm"
include "mapfienlem2.mm"
include "breq1.mm"
include "elrab2.mm"
include "sylanbrc.mm"

theorem mapfienlem3
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
  assert |- ( ( ph /\ g e. T ) -> ( ( `' G o. g ) o. `' F ) e. S )

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
    ccom
    #
    cB
    cA
    cmap
    co
    #
    wcel
    #
    @6
    cZ
    cfsupp
    wbr
    #
    @6
    cS
    wcel
    @2
    @8
    cA
    cB
    @6
    wf
    #
    @2
    cC
    cB
    @4
    wf
    #
    cA
    cC
    @5
    wf
    #
    @10
    @2
    cD
    cB
    @3
    wf
    #
    cC
    cD
    @0
    wf
    #
    @11
    wph
    @13
    @1
    wph
    cB
    cD
    cG
    wf1o
    cD
    cB
    @3
    wf1o
    @13
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
    @2
    @0
    cD
    cC
    cmap
    co
    #
    wcel
    #
    @14
    @1
    @16
    wph
    @16
    @0
    vx
    cv
    #
    cW
    cfsupp
    wbr
    #
    vx
    @15
    crab
    cT
    @18
    vx
    @0
    @15
    elrabi
    mapfien.t
    eleq2s
    adantl
    @0
    cD
    cC
    elmapi
    syl
    cC
    cD
    cB
    @3
    @0
    fco
    syl2anc
    wph
    @12
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
    @12
    mapfien.f
    cC
    cA
    cF
    f1ocnv
    cA
    cC
    @5
    f1of
    3syl
    adantr
    cA
    cC
    cB
    @4
    @5
    fco
    syl2anc
    wph
    @8
    @10
    wb
    @1
    wph
    cB
    cA
    @6
    cvv
    cvv
    mapfien.b
    mapfien.a
    elmapd
    adantr
    mpbird
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vg
    cF
    cG
    cW
    cZ
    mapfien.s
    mapfien.t
    mapfien.w
    mapfien.f
    mapfien.g
    mapfien.a
    mapfien.b
    mapfien.c
    mapfien.d
    mapfien.z
    mapfienlem2
    @17
    cZ
    cfsupp
    wbr
    @9
    vx
    @6
    @7
    cS
    @17
    @6
    cZ
    cfsupp
    breq1
    mapfien.s
    elrab2
    sylanbrc
end
