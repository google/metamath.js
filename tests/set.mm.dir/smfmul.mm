include "cin.mm"
include "cmul.mm"
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
include "remulcld.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cfv.mm"
include "c3.mm"
include "cioo.mm"
include "wral.mm"
include "cc0.mm"
include "c1.mm"
include "cq.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "nfan.mm"
include "csalg.mm"
include "adantr.mm"
include "adantlr.mm"
include "csmblfn.mm"
include "simpr.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "cbvrabv.mm"
include "smfmullem4.mm"
include "issmfdmpt.mm"

theorem smfmul
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
  let vu: setvar u
  let vv: setvar v
  let vk: setvar k
  assume smfmul.x: |- F/ x ph
  assume smfmul.s: |- ( ph -> S e. SAlg )
  assume smfmul.a: |- ( ph -> A e. V )
  assume smfmul.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfmul.d: |- ( ( ph /\ x e. C ) -> D e. RR )
  assume smfmul.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfmul.n: |- ( ph -> ( x e. C |-> D ) e. ( SMblFn ` S ) )

  disjoint A x
  disjoint C x
  disjoint A a
  disjoint A p
  disjoint A q
  disjoint A u
  disjoint A v
  disjoint a p
  disjoint a q
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint q u
  disjoint q v
  disjoint q x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint B a
  disjoint B p
  disjoint B q
  disjoint B u
  disjoint B v
  disjoint C a
  disjoint C p
  disjoint C q
  disjoint C u
  disjoint C v
  disjoint D a
  disjoint D p
  disjoint D q
  disjoint D u
  disjoint D v
  disjoint S a
  disjoint S p
  disjoint S q
  disjoint a ph
  disjoint p ph
  disjoint ph q
  disjoint ph u
  disjoint ph v
  disjoint k x
  assert |- ( ph -> ( x e. ( A i^i C ) |-> ( B x. D ) ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cA
    cC
    cin
    #
    cB
    cD
    cmul
    co
    cS
    va
    smfmul.x
    wph
    va
    nfv
    smfmul.s
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
    smfmul.x
    vx
    cv
    #
    @0
    wcel
    #
    @2
    cA
    wcel
    #
    wph
    @2
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
    @1
    wph
    @7
    cA
    wph
    vx
    @6
    cA
    cB
    cr
    smfmul.x
    @6
    eqid
    smfmul.b
    dmmptdf
    eqcomd
    wph
    @7
    cS
    @6
    smfmul.s
    smfmul.m
    @7
    eqid
    smfdmss
    eqsstrd
    sstrd
    wph
    @3
    wa
    cB
    cD
    wph
    @3
    @4
    cB
    cr
    wcel
    #
    @5
    smfmul.b
    syldan
    wph
    @3
    @2
    cC
    wcel
    #
    cD
    cr
    wcel
    #
    @3
    @9
    wph
    @2
    cA
    cC
    elinel2
    adantl
    smfmul.d
    syldan
    remulcld
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    vx
    vv
    vu
    cA
    cB
    cC
    cD
    @11
    cS
    vq
    vu
    cv
    vv
    cv
    cmul
    co
    @11
    clt
    wbr
    #
    vv
    c2
    vp
    cv
    #
    cfv
    #
    c3
    @14
    cfv
    #
    cioo
    co
    #
    wral
    #
    vu
    cc0
    @14
    cfv
    #
    c1
    @14
    cfv
    #
    cioo
    co
    #
    wral
    #
    vp
    cq
    cc0
    c3
    cfz
    co
    cmap
    co
    #
    crab
    #
    cB
    cc0
    vq
    cv
    #
    cfv
    #
    c1
    @25
    cfv
    #
    cioo
    co
    #
    wcel
    cD
    c2
    @25
    cfv
    #
    c3
    @25
    cfv
    #
    cioo
    co
    #
    wcel
    wa
    vx
    @0
    crab
    cmpt
    #
    @24
    cV
    vq
    wph
    @12
    vx
    smfmul.x
    @12
    vx
    nfv
    nfan
    wph
    cS
    csalg
    wcel
    @12
    smfmul.s
    adantr
    wph
    cA
    cV
    wcel
    @12
    smfmul.a
    adantr
    wph
    @4
    @8
    @12
    smfmul.b
    adantlr
    wph
    @9
    @10
    @12
    smfmul.d
    adantlr
    wph
    @6
    cS
    csmblfn
    cfv
    #
    wcel
    @12
    smfmul.m
    adantr
    wph
    vx
    cC
    cD
    cmpt
    @33
    wcel
    @12
    smfmul.n
    adantr
    wph
    @12
    simpr
    @22
    @13
    vv
    @31
    wral
    #
    vu
    @28
    wral
    #
    vp
    vq
    @23
    @14
    @25
    wceq
    #
    @22
    @34
    vu
    @21
    wral
    @35
    @36
    @18
    @34
    vu
    @21
    @36
    @13
    vv
    @17
    @31
    @36
    @15
    @29
    @16
    @30
    cioo
    c2
    @14
    @25
    fveq1
    c3
    @14
    @25
    fveq1
    oveq12d
    raleqdv
    ralbidv
    @36
    @34
    vu
    @21
    @28
    @36
    @19
    @26
    @20
    @27
    cioo
    cc0
    @14
    @25
    fveq1
    c1
    @14
    @25
    fveq1
    oveq12d
    raleqdv
    bitrd
    cbvrabv
    @32
    eqid
    smfmullem4
    issmfdmpt
end
