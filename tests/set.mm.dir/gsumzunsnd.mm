include "cgsu.mm"
include "co.mm"
include "cres.mm"
include "csn.mm"
include "cmpt.mm"
include "cun.mm"
include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
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
include "fmptd.mm"
include "cvv.mm"
include "wi.mm"
include "expcom.mm"
include "syl.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "gsumzsplit.mm"
include "reseq1i.mm"
include "wss.mm"
include "ssun1.mm"
include "resmpt.mm"
include "mp1i.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "gsumsnd.mm"
include "3eqtrd.mm"

theorem gsumzunsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume gsumzunsnd.b: |- B = ( Base ` G )
  assume gsumzunsnd.p: |- .+ = ( +g ` G )
  assume gsumzunsnd.z: |- Z = ( Cntz ` G )
  assume gsumzunsnd.f: |- F = ( k e. ( A u. { M } ) |-> X )
  assume gsumzunsnd.g: |- ( ph -> G e. Mnd )
  assume gsumzunsnd.a: |- ( ph -> A e. Fin )
  assume gsumzunsnd.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzunsnd.x: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumzunsnd.m: |- ( ph -> M e. V )
  assume gsumzunsnd.d: |- ( ph -> -. M e. A )
  assume gsumzunsnd.y: |- ( ph -> Y e. B )
  assume gsumzunsnd.s: |- ( ( ph /\ k = M ) -> X = Y )

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Y k
  assert |- ( ph -> ( G gsum F ) = ( ( G gsum ( k e. A |-> X ) ) .+ Y ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    cG
    cF
    cA
    cres
    #
    cgsu
    co
    #
    cG
    cF
    cM
    csn
    #
    cres
    #
    cgsu
    co
    #
    c.pl
    co
    cG
    vk
    cA
    cX
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    @2
    cX
    cmpt
    #
    cgsu
    co
    #
    c.pl
    co
    @6
    cY
    c.pl
    co
    wph
    cA
    @2
    cun
    #
    cB
    cA
    @2
    c.pl
    cF
    cG
    cfn
    cG
    c0g
    cfv
    #
    cZ
    gsumzunsnd.b
    @10
    eqid
    gsumzunsnd.p
    gsumzunsnd.z
    gsumzunsnd.g
    wph
    cA
    cfn
    wcel
    @2
    cfn
    wcel
    @9
    cfn
    wcel
    gsumzunsnd.a
    cM
    snfi
    cA
    @2
    unfi
    sylancl
    #
    wph
    vk
    @9
    cX
    cB
    cF
    vk
    cv
    #
    @9
    wcel
    #
    wph
    @12
    cA
    wcel
    #
    @12
    @2
    wcel
    #
    wo
    #
    cX
    cB
    wcel
    #
    @12
    cA
    @2
    elun
    #
    wph
    @14
    @17
    @15
    gsumzunsnd.x
    wph
    @15
    wa
    cX
    cY
    cB
    @15
    wph
    @12
    cM
    wceq
    #
    cX
    cY
    wceq
    @12
    cM
    elsni
    #
    gsumzunsnd.s
    sylan2
    wph
    cY
    cB
    wcel
    #
    @15
    gsumzunsnd.y
    adantr
    eqeltrd
    jaodan
    sylan2b
    gsumzunsnd.f
    fmptd
    gsumzunsnd.c
    wph
    vk
    @9
    cF
    cB
    cvv
    cX
    @10
    gsumzunsnd.f
    @11
    @13
    wph
    @17
    @13
    @16
    wph
    @17
    wi
    #
    @18
    @14
    @22
    @15
    wph
    @14
    @17
    gsumzunsnd.x
    expcom
    @15
    @19
    @22
    @20
    wph
    @19
    @17
    wph
    @19
    wa
    cX
    cY
    cB
    gsumzunsnd.s
    wph
    @21
    @19
    gsumzunsnd.y
    adantr
    eqeltrd
    expcom
    syl
    jaoi
    sylbi
    impcom
    wph
    cG
    c0g
    fvexd
    fsuppmptdm
    wph
    cM
    cA
    wcel
    wn
    cA
    @2
    cin
    c0
    wceq
    gsumzunsnd.d
    cA
    cM
    disjsn
    sylibr
    wph
    @9
    eqidd
    gsumzsplit
    wph
    @1
    @6
    @4
    @8
    c.pl
    wph
    @0
    @5
    cG
    cgsu
    wph
    @0
    vk
    @9
    cX
    cmpt
    #
    cA
    cres
    #
    @5
    cF
    @23
    cA
    gsumzunsnd.f
    reseq1i
    cA
    @9
    wss
    @24
    @5
    wceq
    wph
    cA
    @2
    ssun1
    vk
    @9
    cA
    cX
    resmpt
    mp1i
    syl5eq
    oveq2d
    wph
    @3
    @7
    cG
    cgsu
    wph
    @3
    @23
    @2
    cres
    #
    @7
    cF
    @23
    @2
    gsumzunsnd.f
    reseq1i
    @2
    @9
    wss
    @25
    @7
    wceq
    wph
    @2
    cA
    ssun2
    vk
    @9
    @2
    cX
    resmpt
    mp1i
    syl5eq
    oveq2d
    oveq12d
    wph
    @8
    cY
    @6
    c.pl
    wph
    cX
    cB
    cY
    vk
    cG
    cM
    cV
    gsumzunsnd.b
    gsumzunsnd.g
    gsumzunsnd.m
    gsumzunsnd.y
    gsumzunsnd.s
    gsumsnd
    oveq2d
    3eqtrd
end
