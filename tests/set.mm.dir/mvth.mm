include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "cid.mm"
include "cicc.mm"
include "cres.mm"
include "cdv.mm"
include "cmul.mm"
include "wceq.mm"
include "cioo.mm"
include "wrex.mm"
include "cdiv.mm"
include "cmpt.mm"
include "ccncf.mm"
include "mptresid.mm"
include "wss.mm"
include "cc.mm"
include "wcel.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ax-resscn.mm"
include "cncfmptid.mm"
include "sylancl.mm"
include "syl5eqelr.mm"
include "cdm.mm"
include "c1.mm"
include "oveq2i.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "recnd.mm"
include "1red.mm"
include "dvmptid.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptres2.mm"
include "syl5eqr.mm"
include "dmeqd.mm"
include "1ex.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "cmvth.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ltled.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "fvresi.mm"
include "syl.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "adantr.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "fvmpt3i.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "wf.mm"
include "cncff.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "dvf.mm"
include "feq2d.mm"
include "mpbii.mm"
include "ffvelrnda.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "posdifd.mm"
include "mpbid.mm"
include "gt0ne0d.mm"
include "divmuld.mm"
include "bitr4d.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "rexbidva.mm"

theorem mvth
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  assume mvth.a: |- ( ph -> A e. RR )
  assume mvth.b: |- ( ph -> B e. RR )
  assume mvth.lt: |- ( ph -> A < B )
  assume mvth.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume mvth.d: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint ph x
  disjoint x z
  disjoint A z
  disjoint B z
  disjoint F z
  disjoint ph z
  assert |- ( ph -> E. x e. ( A (,) B ) ( ( RR _D F ) ` x ) = ( ( ( F ` B ) - ( F ` A ) ) / ( B - A ) ) )

  proof
    wph
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cmin
    co
    #
    vx
    cv
    #
    cr
    cid
    cA
    cB
    cicc
    co
    #
    cres
    #
    cdv
    co
    #
    cfv
    #
    cmul
    co
    #
    cB
    @5
    cfv
    #
    cA
    @5
    cfv
    #
    cmin
    co
    #
    @3
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cA
    cB
    cioo
    co
    #
    wrex
    @13
    @2
    cB
    cA
    cmin
    co
    #
    cdiv
    co
    #
    wceq
    #
    vx
    @16
    wrex
    wph
    vx
    cA
    cB
    cF
    @5
    mvth.a
    mvth.b
    mvth.lt
    mvth.f
    wph
    @5
    vz
    @4
    vz
    cv
    #
    cmpt
    #
    @4
    cr
    ccncf
    co
    #
    vz
    @4
    mptresid
    #
    wph
    @4
    cr
    wss
    #
    cr
    cc
    wss
    @21
    @22
    wcel
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @24
    mvth.a
    mvth.b
    cA
    cB
    iccssre
    syl2anc
    #
    ax-resscn
    vz
    @4
    cr
    cncfmptid
    sylancl
    syl5eqelr
    mvth.d
    wph
    @6
    cdm
    vz
    @16
    c1
    cmpt
    #
    cdm
    @16
    wph
    @6
    @28
    wph
    @6
    cr
    @21
    cdv
    co
    @28
    @21
    @5
    cr
    cdv
    @23
    oveq2i
    wph
    vz
    @20
    c1
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    cr
    @16
    @4
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    wph
    @20
    cr
    wcel
    #
    wa
    #
    @20
    wph
    @32
    simpr
    recnd
    @33
    1red
    wph
    vz
    cr
    @31
    dvmptid
    @27
    @30
    @30
    eqid
    #
    tgioo2
    @34
    wph
    @25
    @26
    @4
    @29
    cnt
    cfv
    cfv
    @16
    wceq
    mvth.a
    mvth.b
    cA
    cB
    iccntr
    syl2anc
    dvmptres2
    syl5eqr
    #
    dmeqd
    vz
    @16
    c1
    @28
    1ex
    @28
    eqid
    #
    dmmpti
    syl6eq
    cmvth
    wph
    @15
    @19
    vx
    @16
    wph
    @3
    @16
    wcel
    #
    wa
    #
    @14
    @8
    wceq
    #
    @18
    @13
    wceq
    #
    @15
    @19
    @38
    @39
    @17
    @13
    cmul
    co
    #
    @2
    wceq
    @40
    @38
    @14
    @41
    @8
    @2
    @38
    @11
    @17
    @13
    cmul
    wph
    @11
    @17
    wceq
    @37
    wph
    @9
    cB
    @10
    cA
    cmin
    wph
    cB
    @4
    wcel
    #
    @9
    cB
    wceq
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @42
    wph
    cA
    mvth.a
    rexrd
    #
    wph
    cB
    mvth.b
    rexrd
    #
    wph
    cA
    cB
    mvth.a
    mvth.b
    mvth.lt
    ltled
    #
    cA
    cB
    ubicc2
    syl3anc
    #
    @4
    cB
    fvresi
    syl
    wph
    cA
    @4
    wcel
    #
    @10
    cA
    wceq
    wph
    @43
    @44
    @45
    @50
    @46
    @47
    @48
    cA
    cB
    lbicc2
    syl3anc
    #
    @4
    cA
    fvresi
    syl
    oveq12d
    adantr
    oveq1d
    @38
    @8
    @2
    c1
    cmul
    co
    @2
    @38
    @7
    c1
    @2
    cmul
    wph
    @37
    @7
    @3
    @28
    cfv
    c1
    wph
    @3
    @6
    @28
    @35
    fveq1d
    vz
    @3
    c1
    c1
    @16
    @28
    @20
    @3
    wceq
    c1
    eqidd
    @36
    1ex
    fvmpt3i
    sylan9eq
    oveq2d
    @38
    @2
    wph
    @2
    cc
    wcel
    @37
    wph
    @2
    wph
    @0
    @1
    wph
    @4
    cr
    cB
    cF
    wph
    cF
    @22
    wcel
    @4
    cr
    cF
    wf
    mvth.f
    @4
    cr
    cF
    cncff
    syl
    #
    @49
    ffvelrnd
    wph
    @4
    cr
    cA
    cF
    @52
    @51
    ffvelrnd
    resubcld
    recnd
    adantr
    #
    mulid1d
    eqtrd
    eqeq12d
    @38
    @2
    @17
    @13
    @53
    wph
    @17
    cc
    wcel
    @37
    wph
    @17
    wph
    cB
    cA
    mvth.b
    mvth.a
    resubcld
    recnd
    adantr
    wph
    @16
    cc
    @3
    @12
    wph
    @12
    cdm
    #
    cc
    @12
    wf
    @16
    cc
    @12
    wf
    cF
    dvf
    wph
    @54
    @16
    cc
    @12
    mvth.d
    feq2d
    mpbii
    ffvelrnda
    wph
    @17
    cc0
    wne
    @37
    wph
    @17
    wph
    cA
    cB
    clt
    wbr
    cc0
    @17
    clt
    wbr
    mvth.lt
    wph
    cA
    cB
    mvth.a
    mvth.b
    posdifd
    mpbid
    gt0ne0d
    adantr
    divmuld
    bitr4d
    @8
    @14
    eqcom
    @13
    @18
    eqcom
    3bitr4g
    rexbidva
    mpbid
end
