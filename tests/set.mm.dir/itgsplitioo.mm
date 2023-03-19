include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "caddc.mm"
include "wceq.mm"
include "wn.mm"
include "cle.mm"
include "wo.mm"
include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simp1d.mm"
include "leloed.mm"
include "ord.mm"
include "cc0.mm"
include "cc.mm"
include "cv.mm"
include "cxr.mm"
include "wss.mm"
include "rexrd.mm"
include "iooss1.mm"
include "sselda.mm"
include "syldan.mm"
include "itgcl.mm"
include "addid2d.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "itgeq1.mm"
include "syl.mm"
include "c0.mm"
include "iooid.mm"
include "syl6eq.mm"
include "itg0.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "simp3d.mm"
include "iooss2.mm"
include "addid1d.mm"
include "oveq2.mm"
include "syl5eqr.mm"
include "oveq2d.mm"
include "syl5ibcom.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cin.mm"
include "covol.mm"
include "cfv.mm"
include "indir.mm"
include "jca.mm"
include "adantr.mm"
include "leidd.mm"
include "ioodisj.mm"
include "syl21anc.mm"
include "incom.mm"
include "ltnrd.mm"
include "eliooord.mm"
include "simpld.mm"
include "nsyl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "uneq12d.mm"
include "un0.mm"
include "fveq2d.mm"
include "ovol0.mm"
include "3jca.mm"
include "ioojoin.mm"
include "sylan.mm"
include "adantlr.mm"
include "cmpt.mm"
include "cibl.mm"
include "ssun1.mm"
include "a1i.mm"
include "ioossre.mm"
include "snssd.mm"
include "unssd.mm"
include "cdif.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "difss.mm"
include "eqsstri.mm"
include "ovolsn.mm"
include "ovolssnul.mm"
include "syl3anc.mm"
include "syl5sseq.mm"
include "itgss3.mm"
include "itgsplit.mm"
include "simprd.mm"
include "eqtr4d.mm"
include "ex.mm"
include "ecased.mm"

theorem itgsplitioo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume itgsplitioo.1: |- ( ph -> A e. RR )
  assume itgsplitioo.2: |- ( ph -> C e. RR )
  assume itgsplitioo.3: |- ( ph -> B e. ( A [,] C ) )
  assume itgsplitioo.4: |- ( ( ph /\ x e. ( A (,) C ) ) -> D e. CC )
  assume itgsplitioo.5: |- ( ph -> ( x e. ( A (,) B ) |-> D ) e. L^1 )
  assume itgsplitioo.6: |- ( ph -> ( x e. ( B (,) C ) |-> D ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> S. ( A (,) C ) D _d x = ( S. ( A (,) B ) D _d x + S. ( B (,) C ) D _d x ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    vx
    cA
    cC
    cioo
    co
    #
    cD
    citg
    #
    vx
    cA
    cB
    cioo
    co
    #
    cD
    citg
    #
    vx
    cB
    cC
    cioo
    co
    #
    cD
    citg
    #
    caddc
    co
    #
    wceq
    #
    wph
    @0
    wn
    cA
    cB
    wceq
    #
    @9
    wph
    @0
    @10
    wph
    cA
    cB
    cle
    wbr
    #
    @0
    @10
    wo
    wph
    cB
    cr
    wcel
    #
    @11
    cB
    cC
    cle
    wbr
    #
    wph
    cB
    cA
    cC
    cicc
    co
    wcel
    #
    @12
    @11
    @13
    w3a
    #
    itgsplitioo.3
    wph
    cA
    cr
    wcel
    cC
    cr
    wcel
    @14
    @15
    wb
    itgsplitioo.1
    itgsplitioo.2
    cA
    cC
    cB
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    #
    wph
    cA
    cB
    itgsplitioo.1
    wph
    @12
    @11
    @13
    @16
    simp1d
    #
    leloed
    mpbid
    ord
    wph
    @9
    @10
    @7
    cc0
    @7
    caddc
    co
    #
    wceq
    wph
    @19
    @7
    wph
    @7
    wph
    vx
    @6
    cD
    cc
    wph
    vx
    cv
    #
    @6
    wcel
    @20
    @2
    wcel
    #
    cD
    cc
    wcel
    #
    wph
    @6
    @2
    @20
    wph
    cA
    cxr
    wcel
    #
    @11
    @6
    @2
    wss
    wph
    cA
    itgsplitioo.1
    rexrd
    #
    @17
    cA
    cB
    cC
    iooss1
    syl2anc
    sselda
    itgsplitioo.4
    syldan
    itgsplitioo.6
    itgcl
    addid2d
    eqcomd
    @10
    @3
    @7
    @8
    @19
    @10
    @2
    @6
    wceq
    @3
    @7
    wceq
    cA
    cB
    cC
    cioo
    oveq1
    vx
    @2
    @6
    cD
    itgeq1
    syl
    @10
    @5
    cc0
    @7
    caddc
    @10
    @5
    vx
    c0
    cD
    citg
    #
    cc0
    @10
    @4
    c0
    wceq
    @5
    @25
    wceq
    @10
    @4
    cB
    cB
    cioo
    co
    #
    c0
    cA
    cB
    cB
    cioo
    oveq1
    cB
    iooid
    #
    syl6eq
    vx
    @4
    c0
    cD
    itgeq1
    syl
    vx
    cD
    itg0
    #
    syl6eq
    oveq1d
    eqeq12d
    syl5ibrcom
    syld
    wph
    @1
    wn
    cB
    cC
    wceq
    #
    @9
    wph
    @1
    @29
    wph
    @13
    @1
    @29
    wo
    wph
    @12
    @11
    @13
    @16
    simp3d
    #
    wph
    cB
    cC
    @18
    itgsplitioo.2
    leloed
    mpbid
    ord
    wph
    @5
    @5
    cc0
    caddc
    co
    #
    wceq
    @29
    @9
    wph
    @31
    @5
    wph
    @5
    wph
    vx
    @4
    cD
    cc
    wph
    @20
    @4
    wcel
    @21
    @22
    wph
    @4
    @2
    @20
    wph
    cC
    cxr
    wcel
    #
    @13
    @4
    @2
    wss
    wph
    cC
    itgsplitioo.2
    rexrd
    #
    @30
    cA
    cB
    cC
    iooss2
    syl2anc
    sselda
    itgsplitioo.4
    syldan
    itgsplitioo.5
    itgcl
    addid1d
    eqcomd
    @29
    @5
    @3
    @31
    @8
    @29
    @4
    @2
    wceq
    @5
    @3
    wceq
    cB
    cC
    cA
    cioo
    oveq2
    vx
    @4
    @2
    cD
    itgeq1
    syl
    @29
    cc0
    @7
    @5
    caddc
    @29
    cc0
    @25
    @7
    @28
    @29
    c0
    @6
    wceq
    @25
    @7
    wceq
    @29
    c0
    @26
    @6
    @27
    cB
    cC
    cB
    cioo
    oveq2
    syl5eqr
    vx
    c0
    @6
    cD
    itgeq1
    syl
    syl5eqr
    oveq2d
    eqeq12d
    syl5ibcom
    syld
    wph
    @0
    @1
    wa
    #
    @9
    wph
    @34
    wa
    #
    @3
    vx
    @4
    cB
    csn
    #
    cun
    #
    cD
    citg
    #
    @7
    caddc
    co
    @8
    @35
    vx
    @37
    @6
    cD
    @2
    cc
    @35
    @37
    @6
    cin
    #
    covol
    cfv
    c0
    covol
    cfv
    cc0
    @35
    @39
    c0
    covol
    @35
    @39
    @4
    @6
    cin
    #
    @36
    @6
    cin
    #
    cun
    #
    c0
    @4
    @36
    @6
    indir
    @35
    @42
    c0
    c0
    cun
    c0
    @35
    @40
    c0
    @41
    c0
    @35
    @23
    cB
    cxr
    wcel
    #
    wa
    #
    @43
    @32
    wa
    #
    cB
    cB
    cle
    wbr
    @40
    c0
    wceq
    wph
    @44
    @34
    wph
    @23
    @43
    @24
    wph
    cB
    @18
    rexrd
    #
    jca
    adantr
    wph
    @45
    @34
    wph
    @43
    @32
    @46
    @33
    jca
    adantr
    @35
    cB
    wph
    @12
    @34
    @18
    adantr
    #
    leidd
    cA
    cB
    cB
    cC
    ioodisj
    syl21anc
    @35
    @41
    @6
    @36
    cin
    #
    c0
    @36
    @6
    incom
    @35
    cB
    @6
    wcel
    #
    wn
    @48
    c0
    wceq
    @35
    cB
    cB
    clt
    wbr
    #
    @49
    @35
    cB
    @47
    ltnrd
    @49
    @50
    @1
    cB
    cB
    cC
    eliooord
    simpld
    nsyl
    @6
    cB
    disjsn
    sylibr
    syl5eq
    uneq12d
    c0
    un0
    syl6eq
    syl5eq
    fveq2d
    ovol0
    syl6eq
    @35
    @37
    @6
    cun
    #
    @2
    wph
    @23
    @43
    @32
    w3a
    @34
    @51
    @2
    wceq
    wph
    @23
    @43
    @32
    @24
    @46
    @33
    3jca
    cA
    cB
    cC
    ioojoin
    sylan
    #
    eqcomd
    wph
    @21
    @22
    @34
    itgsplitioo.4
    adantlr
    #
    @35
    vx
    @4
    cD
    cmpt
    cibl
    wcel
    #
    vx
    @37
    cD
    cmpt
    cibl
    wcel
    #
    wph
    @54
    @34
    itgsplitioo.5
    adantr
    @35
    @54
    @55
    wb
    #
    @5
    @38
    wceq
    #
    @35
    vx
    @4
    @37
    cD
    @4
    @37
    wss
    @35
    @4
    @36
    ssun1
    a1i
    @35
    @4
    @36
    cr
    @4
    cr
    wss
    @35
    cA
    cB
    ioossre
    a1i
    @35
    cB
    cr
    @47
    snssd
    #
    unssd
    @35
    @37
    @4
    cdif
    #
    @36
    wss
    #
    @36
    cr
    wss
    @36
    covol
    cfv
    cc0
    wceq
    #
    @59
    covol
    cfv
    cc0
    wceq
    @60
    @35
    @59
    @36
    @4
    cdif
    #
    @36
    @59
    @36
    @4
    cun
    #
    @4
    cdif
    @62
    @37
    @63
    @4
    @4
    @36
    uncom
    difeq1i
    @36
    @4
    difun2
    eqtri
    @36
    @4
    difss
    eqsstri
    a1i
    @58
    @35
    @12
    @61
    @47
    cB
    ovolsn
    syl
    @59
    @36
    ovolssnul
    syl3anc
    @35
    @20
    @37
    wcel
    @21
    @22
    @35
    @37
    @2
    @20
    @35
    @51
    @37
    @2
    @37
    @6
    ssun1
    @52
    syl5sseq
    sselda
    @53
    syldan
    itgss3
    #
    simpld
    mpbid
    wph
    vx
    @6
    cD
    cmpt
    cibl
    wcel
    @34
    itgsplitioo.6
    adantr
    itgsplit
    @35
    @5
    @38
    @7
    caddc
    @35
    @56
    @57
    @64
    simprd
    oveq1d
    eqtr4d
    ex
    ecased
end
