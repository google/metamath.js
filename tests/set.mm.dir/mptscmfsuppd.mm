include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "csca.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "eqid.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "feqmptd.mm"
include "eqbrtrrd.mm"
include "mptscmfsupp0.mm"

theorem mptscmfsuppd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mptscmfsuppd.b: |- B = ( Base ` P )
  assume mptscmfsuppd.s: |- S = ( Scalar ` P )
  assume mptscmfsuppd.n: |- .x. = ( .s ` P )
  assume mptscmfsuppd.p: |- ( ph -> P e. LMod )
  assume mptscmfsuppd.x: |- ( ph -> X e. V )
  assume mptscmfsuppd.z: |- ( ( ph /\ k e. X ) -> Z e. B )
  assume mptscmfsuppd.a: |- ( ph -> A : X --> Y )
  assume mptscmfsuppd.f: |- ( ph -> A finSupp ( 0g ` S ) )

  disjoint A k
  disjoint B k
  disjoint P k
  disjoint S k
  disjoint X k
  disjoint .x. k
  disjoint k ph
  assert |- ( ph -> ( k e. X |-> ( ( A ` k ) .x. Z ) ) finSupp ( 0g ` P ) )

  proof
    wph
    cvv
    cX
    cP
    cS
    vk
    cv
    #
    cA
    cfv
    #
    vk
    c.x
    cB
    cV
    cZ
    cP
    c0g
    cfv
    #
    cS
    c0g
    cfv
    #
    mptscmfsuppd.x
    mptscmfsuppd.p
    cS
    cP
    csca
    cfv
    wceq
    wph
    mptscmfsuppd.s
    a1i
    mptscmfsuppd.b
    wph
    @0
    cX
    wcel
    wa
    @0
    cA
    fvexd
    mptscmfsuppd.z
    @2
    eqid
    @3
    eqid
    mptscmfsuppd.n
    wph
    cA
    vk
    cX
    @1
    cmpt
    @3
    cfsupp
    wph
    vk
    cX
    cY
    cA
    mptscmfsuppd.a
    feqmptd
    mptscmfsuppd.f
    eqbrtrrd
    mptscmfsupp0
end
