include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "wa.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "gsumcom2.mm"

theorem gsumcom
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
  let cF: class F
  assume gsumxp.b: |- B = ( Base ` G )
  assume gsumxp.z: |- .0. = ( 0g ` G )
  assume gsumxp.g: |- ( ph -> G e. CMnd )
  assume gsumxp.a: |- ( ph -> A e. V )
  assume gsumxp.r: |- ( ph -> C e. W )
  assume gsumcom.f: |- ( ( ph /\ ( j e. A /\ k e. C ) ) -> X e. B )
  assume gsumcom.u: |- ( ph -> U e. Fin )
  assume gsumcom.n: |- ( ( ph /\ ( ( j e. A /\ k e. C ) /\ -. j U k ) ) -> X = .0. )

  disjoint j k
  disjoint .0. j
  disjoint .0. k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint U j
  disjoint U k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint C j
  disjoint C k
  disjoint V j
  disjoint F j
  disjoint F k
  assert |- ( ph -> ( G gsum ( j e. A , k e. C |-> X ) ) = ( G gsum ( k e. C , j e. A |-> X ) ) )

  proof
    wph
    cA
    cB
    cC
    cC
    cU
    vj
    vk
    cA
    cG
    cV
    cW
    cX
    cW
    c.0
    gsumxp.b
    gsumxp.z
    gsumxp.g
    gsumxp.a
    wph
    cC
    cW
    wcel
    vj
    cv
    cA
    wcel
    #
    gsumxp.r
    adantr
    gsumcom.f
    gsumcom.u
    gsumcom.n
    gsumxp.r
    @0
    vk
    cv
    cC
    wcel
    #
    wa
    @1
    @0
    wa
    wb
    wph
    @0
    @1
    ancom
    a1i
    gsumcom2
end
