include "cxp.mm"
include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "wcel.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "brxp.mm"
include "biimpri.mm"
include "adantl.mm"
include "pm2.24d.mm"
include "impr.mm"
include "gsumcom3.mm"

theorem gsumcom3fi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cX: class X
  assume gsumcom3fi.b: |- B = ( Base ` G )
  assume gsumcom3fi.g: |- ( ph -> G e. CMnd )
  assume gsumcom3fi.a: |- ( ph -> A e. Fin )
  assume gsumcom3fi.r: |- ( ph -> C e. Fin )
  assume gsumcom3fi.f: |- ( ( ph /\ ( j e. A /\ k e. C ) ) -> X e. B )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint C j
  disjoint C k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( G gsum ( j e. A |-> ( G gsum ( k e. C |-> X ) ) ) ) = ( G gsum ( k e. C |-> ( G gsum ( j e. A |-> X ) ) ) ) )

  proof
    wph
    cA
    cB
    cC
    cA
    cC
    cxp
    #
    vj
    vk
    cG
    cfn
    cfn
    cX
    cG
    c0g
    cfv
    #
    gsumcom3fi.b
    @1
    eqid
    gsumcom3fi.g
    gsumcom3fi.a
    gsumcom3fi.r
    gsumcom3fi.f
    wph
    cA
    cfn
    wcel
    cC
    cfn
    wcel
    @0
    cfn
    wcel
    gsumcom3fi.a
    gsumcom3fi.r
    cA
    cC
    xpfi
    syl2anc
    wph
    vj
    cv
    #
    cA
    wcel
    vk
    cv
    #
    cC
    wcel
    wa
    #
    @2
    @3
    @0
    wbr
    #
    wn
    cX
    @1
    wceq
    #
    wph
    @4
    wa
    @5
    @6
    @4
    @5
    wph
    @5
    @4
    @2
    @3
    cA
    cC
    brxp
    biimpri
    adantl
    pm2.24d
    impr
    gsumcom3
end
