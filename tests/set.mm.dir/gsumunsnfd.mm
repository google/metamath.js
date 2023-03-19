include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "cv.mm"
include "wo.mm"
include "elun.mm"
include "wa.mm"
include "wceq.mm"
include "elsni.mm"
include "sylan2.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "gsummptfidmsplit.mm"
include "ccmn.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "nfv.mm"
include "gsumsnfd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem gsumunsnfd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  assume gsumunsnd.b: |- B = ( Base ` G )
  assume gsumunsnd.p: |- .+ = ( +g ` G )
  assume gsumunsnd.g: |- ( ph -> G e. CMnd )
  assume gsumunsnd.a: |- ( ph -> A e. Fin )
  assume gsumunsnd.f: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumunsnd.m: |- ( ph -> M e. V )
  assume gsumunsnd.d: |- ( ph -> -. M e. A )
  assume gsumunsnd.y: |- ( ph -> Y e. B )
  assume gsumunsnd.s: |- ( ( ph /\ k = M ) -> X = Y )
  assume gsumunsnfd.0: |- F/_ k Y

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint M k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. ( A u. { M } ) |-> X ) ) = ( ( G gsum ( k e. A |-> X ) ) .+ Y ) )

  proof
    wph
    cG
    vk
    cA
    cM
    csn
    #
    cun
    #
    cX
    cmpt
    cgsu
    co
    cG
    vk
    cA
    cX
    cmpt
    cgsu
    co
    #
    cG
    vk
    @0
    cX
    cmpt
    cgsu
    co
    #
    c.pl
    co
    @2
    cY
    c.pl
    co
    wph
    @1
    cB
    cA
    @0
    c.pl
    vk
    cG
    cX
    gsumunsnd.b
    gsumunsnd.p
    gsumunsnd.g
    wph
    cA
    cfn
    wcel
    @0
    cfn
    wcel
    @1
    cfn
    wcel
    gsumunsnd.a
    cM
    snfi
    cA
    @0
    unfi
    sylancl
    vk
    cv
    #
    @1
    wcel
    wph
    @4
    cA
    wcel
    #
    @4
    @0
    wcel
    #
    wo
    cX
    cB
    wcel
    #
    @4
    cA
    @0
    elun
    wph
    @5
    @7
    @6
    gsumunsnd.f
    wph
    @6
    wa
    cX
    cY
    cB
    @6
    wph
    @4
    cM
    wceq
    cX
    cY
    wceq
    @4
    cM
    elsni
    gsumunsnd.s
    sylan2
    wph
    cY
    cB
    wcel
    @6
    gsumunsnd.y
    adantr
    eqeltrd
    jaodan
    sylan2b
    wph
    cM
    cA
    wcel
    wn
    cA
    @0
    cin
    c0
    wceq
    gsumunsnd.d
    cA
    cM
    disjsn
    sylibr
    wph
    @1
    eqidd
    gsummptfidmsplit
    wph
    @3
    cY
    @2
    c.pl
    wph
    cX
    cB
    cY
    vk
    cG
    cM
    cV
    gsumunsnd.b
    wph
    cG
    ccmn
    wcel
    cG
    cmnd
    wcel
    gsumunsnd.g
    cG
    cmnmnd
    syl
    gsumunsnd.m
    gsumunsnd.y
    gsumunsnd.s
    wph
    vk
    nfv
    gsumunsnfd.0
    gsumsnfd
    oveq2d
    eqtrd
end
