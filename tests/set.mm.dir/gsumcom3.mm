include "cmpt2.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "gsumcom.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "gsum2d2.mm"
include "ccnv.mm"
include "ancom2s.mm"
include "cfn.mm"
include "cnvfi.mm"
include "syl.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "ancom.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "anbi12i.mm"
include "sylan2b.mm"
include "3eqtr3d.mm"

theorem gsumcom3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume gsumcom3.b: |- B = ( Base ` G )
  assume gsumcom3.z: |- .0. = ( 0g ` G )
  assume gsumcom3.g: |- ( ph -> G e. CMnd )
  assume gsumcom3.a: |- ( ph -> A e. V )
  assume gsumcom3.r: |- ( ph -> C e. W )
  assume gsumcom3.f: |- ( ( ph /\ ( j e. A /\ k e. C ) ) -> X e. B )
  assume gsumcom3.u: |- ( ph -> U e. Fin )
  assume gsumcom3.n: |- ( ( ph /\ ( ( j e. A /\ k e. C ) /\ -. j U k ) ) -> X = .0. )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint C j
  disjoint C k
  disjoint G j
  disjoint G k
  disjoint U j
  disjoint U k
  disjoint V j
  disjoint .0. j
  disjoint .0. k
  disjoint j ph
  disjoint k ph
  disjoint W k
  assert |- ( ph -> ( G gsum ( j e. A |-> ( G gsum ( k e. C |-> X ) ) ) ) = ( G gsum ( k e. C |-> ( G gsum ( j e. A |-> X ) ) ) ) )

  proof
    wph
    cG
    vj
    vk
    cA
    cC
    cX
    cmpt2
    cgsu
    co
    cG
    vk
    vj
    cC
    cA
    cX
    cmpt2
    cgsu
    co
    cG
    vj
    cA
    cG
    vk
    cC
    cX
    cmpt
    cgsu
    co
    cmpt
    cgsu
    co
    cG
    vk
    cC
    cG
    vj
    cA
    cX
    cmpt
    cgsu
    co
    cmpt
    cgsu
    co
    wph
    cA
    cB
    cC
    cU
    vj
    vk
    cG
    cV
    cW
    cX
    c.0
    gsumcom3.b
    gsumcom3.z
    gsumcom3.g
    gsumcom3.a
    gsumcom3.r
    gsumcom3.f
    gsumcom3.u
    gsumcom3.n
    gsumcom
    wph
    cA
    cB
    cC
    cU
    vj
    vk
    cG
    cV
    cW
    cX
    c.0
    gsumcom3.b
    gsumcom3.z
    gsumcom3.g
    gsumcom3.a
    wph
    cC
    cW
    wcel
    vj
    cv
    #
    cA
    wcel
    #
    gsumcom3.r
    adantr
    gsumcom3.f
    gsumcom3.u
    gsumcom3.n
    gsum2d2
    wph
    cC
    cB
    cA
    cU
    ccnv
    #
    vk
    vj
    cG
    cW
    cV
    cX
    c.0
    gsumcom3.b
    gsumcom3.z
    gsumcom3.g
    gsumcom3.r
    wph
    cA
    cV
    wcel
    vk
    cv
    #
    cC
    wcel
    #
    gsumcom3.a
    adantr
    wph
    @1
    @4
    cX
    cB
    wcel
    gsumcom3.f
    ancom2s
    wph
    cU
    cfn
    wcel
    @2
    cfn
    wcel
    gsumcom3.u
    cU
    cnvfi
    syl
    @4
    @1
    wa
    #
    @3
    @0
    @2
    wbr
    #
    wn
    #
    wa
    wph
    @1
    @4
    wa
    #
    @0
    @3
    cU
    wbr
    #
    wn
    #
    wa
    cX
    c.0
    wceq
    @5
    @8
    @7
    @10
    @4
    @1
    ancom
    @6
    @9
    @3
    @0
    cU
    vk
    vex
    vj
    vex
    brcnv
    notbii
    anbi12i
    gsumcom3.n
    sylan2b
    gsum2d2
    3eqtr3d
end
