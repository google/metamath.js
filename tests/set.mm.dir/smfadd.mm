include "cin.mm"
include "caddc.mm"
include "co.mm"
include "nfv.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "elinel1.mm"
include "adantl.mm"
include "ssdf.mm"
include "cmpt.mm"
include "cdm.mm"
include "cr.mm"
include "eqid.mm"
include "dmmptdf.mm"
include "eqcomd.mm"
include "smfdmss.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "wa.mm"
include "syldan.mm"
include "elinel2.mm"
include "readdcld.mm"
include "fmptdf.mm"
include "mptex2.mm"
include "cq.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "nfan.mm"
include "csalg.mm"
include "adantr.mm"
include "adantlr.mm"
include "csmblfn.mm"
include "cfv.mm"
include "simpr.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "mpteq2i.mm"
include "smfaddlem2.mm"
include "issmfdmpt.mm"

theorem smfadd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cV: class V
  let va: setvar a
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  assume smfadd.x: |- F/ x ph
  assume smfadd.s: |- ( ph -> S e. SAlg )
  assume smfadd.a: |- ( ph -> A e. V )
  assume smfadd.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfadd.d: |- ( ( ph /\ x e. C ) -> D e. RR )
  assume smfadd.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfadd.n: |- ( ph -> ( x e. C |-> D ) e. ( SMblFn ` S ) )

  disjoint A x
  disjoint C x
  disjoint A a
  disjoint A p
  disjoint A q
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint p q
  disjoint p x
  disjoint q x
  disjoint B a
  disjoint B p
  disjoint B q
  disjoint C a
  disjoint C p
  disjoint C q
  disjoint D a
  disjoint D p
  disjoint D q
  disjoint S a
  disjoint S p
  disjoint S q
  disjoint a ph
  disjoint p ph
  disjoint ph q
  disjoint a r
  disjoint p r
  disjoint q r
  disjoint r x
  disjoint k x
  assert |- ( ph -> ( x e. ( A i^i C ) |-> ( B + D ) ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cC
    cin
    #
    cB
    cD
    caddc
    co
    #
    cS
    va
    smfadd.x
    wph
    va
    nfv
    smfadd.s
    wph
    @0
    cA
    cS
    cuni
    #
    wph
    vx
    @0
    cA
    smfadd.x
    vx
    cv
    #
    @0
    wcel
    #
    @3
    cA
    wcel
    #
    wph
    @3
    cA
    cC
    elinel1
    adantl
    #
    ssdf
    wph
    cA
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    @2
    wph
    @8
    cA
    wph
    vx
    @7
    cA
    cB
    cr
    smfadd.x
    @7
    eqid
    smfadd.b
    dmmptdf
    eqcomd
    wph
    @8
    cS
    @7
    smfadd.s
    smfadd.m
    @8
    eqid
    smfdmss
    eqsstrd
    sstrd
    wph
    vx
    @0
    @1
    cr
    wph
    vx
    @0
    @1
    cr
    vx
    @0
    @1
    cmpt
    #
    smfadd.x
    wph
    @4
    wa
    cB
    cD
    wph
    @4
    @5
    cB
    cr
    wcel
    #
    @6
    smfadd.b
    syldan
    wph
    @4
    @3
    cC
    wcel
    #
    cD
    cr
    wcel
    #
    @4
    @11
    wph
    @3
    cA
    cC
    elinel2
    adantl
    smfadd.d
    syldan
    readdcld
    @9
    eqid
    fmptdf
    mptex2
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    vx
    cA
    cB
    cC
    cD
    @13
    cS
    vp
    cq
    vp
    cv
    #
    vr
    cv
    #
    caddc
    co
    #
    @13
    clt
    wbr
    #
    vr
    cq
    crab
    #
    cmpt
    cV
    vq
    vp
    wph
    @14
    vx
    smfadd.x
    @14
    vx
    nfv
    nfan
    wph
    cS
    csalg
    wcel
    @14
    smfadd.s
    adantr
    wph
    cA
    cV
    wcel
    @14
    smfadd.a
    adantr
    wph
    @5
    @10
    @14
    smfadd.b
    adantlr
    wph
    @11
    @12
    @14
    smfadd.d
    adantlr
    wph
    @7
    cS
    csmblfn
    cfv
    #
    wcel
    @14
    smfadd.m
    adantr
    wph
    vx
    cC
    cD
    cmpt
    @20
    wcel
    @14
    smfadd.n
    adantr
    wph
    @14
    simpr
    vp
    cq
    @19
    @15
    vq
    cv
    #
    caddc
    co
    #
    @13
    clt
    wbr
    #
    vq
    cq
    crab
    @18
    @23
    vr
    vq
    cq
    @16
    @21
    wceq
    @17
    @22
    @13
    clt
    @16
    @21
    @15
    caddc
    oveq2
    breq1d
    cbvrabv
    mpteq2i
    smfaddlem2
    issmfdmpt
end
