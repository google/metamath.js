include "climc.mm"
include "co.mm"
include "cres.mm"
include "cflf.mm"
include "cfv.mm"
include "cv.mm"
include "cc.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "cnei.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "rgenw.mm"
include "eqid.mm"
include "wceq.mm"
include "imaeq2.mm"
include "inss2.mm"
include "resima2.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "rexrnmpt.mm"
include "mp1i.mm"
include "crest.mm"
include "fvex.mm"
include "difss.mm"
include "eqsstri.mm"
include "syl5ss.mm"
include "cnex.mm"
include "ssex.mm"
include "syl.mm"
include "ad2antrr.mm"
include "restval.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "rexeqdv.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "opnneip.mm"
include "mp3an1.mm"
include "id.mm"
include "a1i.mm"
include "ineq12d.mm"
include "imaeq2d.mm"
include "rspcev.mm"
include "sylan.mm"
include "anasss.mm"
include "rexlimiva.mm"
include "cnt.mm"
include "simprl.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "neii1.mm"
include "ntropn.mm"
include "clp.mm"
include "lpss.mm"
include "sseldd.mm"
include "snssd.mm"
include "ad3antrrr.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "snssg.mm"
include "mpbird.mm"
include "ntrss2.mm"
include "ssrin.mm"
include "imass2.mm"
include "3syl.mm"
include "simprr.mm"
include "sstrd.mm"
include "eleq2.mm"
include "ineq2i.mm"
include "ineq1.mm"
include "syl5eqr.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "impbid2.mm"
include "3bitr4rd.mm"
include "anassrs.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "ellimc2.mm"
include "ctopon.mm"
include "cfil.mm"
include "wf.mm"
include "limcflflem.mm"
include "fssres.mm"
include "sylancl.mm"
include "isflf.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem limcflf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cK: class K
  let cL: class L
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  assume limcflf.f: |- ( ph -> F : A --> CC )
  assume limcflf.a: |- ( ph -> A C_ CC )
  assume limcflf.b: |- ( ph -> B e. ( ( limPt ` K ) ` A ) )
  assume limcflf.k: |- K = ( TopOpen ` CCfld )
  assume limcflf.c: |- C = ( A \ { B } )
  assume limcflf.l: |- L = ( ( ( nei ` K ) ` { B } ) |`t C )


  assert |- ( ph -> ( F limCC B ) = ( ( K fLimf L ) ` ( F |` C ) ) )

  proof
    wph
    vx
    cF
    cB
    climc
    co
    #
    cF
    cC
    cres
    #
    cK
    cL
    cflf
    co
    cfv
    #
    wph
    vx
    cv
    #
    cc
    wcel
    #
    @3
    vu
    cv
    #
    wcel
    #
    cB
    vw
    cv
    #
    wcel
    #
    cF
    @7
    cA
    cB
    csn
    #
    cdif
    #
    cin
    #
    cima
    #
    @5
    wss
    #
    wa
    #
    vw
    cK
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wa
    @4
    @6
    @1
    vs
    cv
    #
    cima
    #
    @5
    wss
    #
    vs
    cL
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wa
    #
    @3
    @0
    wcel
    @3
    @2
    wcel
    #
    wph
    @4
    @17
    @23
    wph
    @4
    wa
    #
    @16
    @22
    vu
    cK
    @26
    @5
    cK
    wcel
    #
    wa
    @6
    @15
    @21
    @26
    @27
    @6
    @15
    @21
    wb
    @26
    @27
    @6
    wa
    #
    wa
    #
    @20
    vs
    vt
    @9
    cK
    cnei
    cfv
    #
    cfv
    #
    vt
    cv
    #
    cC
    cin
    #
    cmpt
    #
    crn
    #
    wrex
    #
    cF
    @33
    cima
    #
    @5
    wss
    #
    vt
    @31
    wrex
    #
    @21
    @15
    @33
    cvv
    wcel
    #
    vt
    @31
    wral
    @36
    @39
    wb
    @29
    @40
    vt
    @31
    @32
    cC
    vt
    vex
    inex1
    rgenw
    @20
    @38
    vt
    vs
    @31
    @33
    @34
    cvv
    @34
    eqid
    @18
    @33
    wceq
    #
    @19
    @37
    @5
    @41
    @19
    @1
    @33
    cima
    #
    @37
    @18
    @33
    @1
    imaeq2
    @33
    cC
    wss
    @42
    @37
    wceq
    @32
    cC
    inss2
    cF
    @33
    cC
    resima2
    ax-mp
    syl6eq
    sseq1d
    rexrnmpt
    mp1i
    @29
    @20
    vs
    cL
    @35
    @29
    cL
    @31
    cC
    crest
    co
    #
    @35
    limcflf.l
    @29
    @31
    cvv
    wcel
    cC
    cvv
    wcel
    #
    @43
    @35
    wceq
    @9
    @30
    fvex
    wph
    @44
    @4
    @28
    wph
    cC
    cc
    wss
    @44
    wph
    cC
    cA
    cc
    cC
    @10
    cA
    limcflf.c
    cA
    @9
    difss
    eqsstri
    #
    limcflf.a
    syl5ss
    cC
    cc
    cnex
    ssex
    syl
    ad2antrr
    vt
    cC
    @31
    cvv
    cvv
    restval
    sylancr
    syl5eq
    rexeqdv
    @29
    @15
    @39
    @14
    @39
    vw
    cK
    @7
    cK
    wcel
    #
    @8
    @13
    @39
    @46
    @8
    wa
    @7
    @31
    wcel
    #
    @13
    @39
    cK
    ctop
    wcel
    #
    @46
    @8
    @47
    cK
    limcflf.k
    cnfldtop
    #
    cB
    cK
    @7
    opnneip
    mp3an1
    @38
    @13
    vt
    @7
    @31
    @32
    @7
    wceq
    #
    @37
    @12
    @5
    @50
    @33
    @11
    cF
    @50
    @32
    @7
    cC
    @10
    @50
    id
    cC
    @10
    wceq
    @50
    limcflf.c
    a1i
    ineq12d
    imaeq2d
    sseq1d
    rspcev
    sylan
    anasss
    rexlimiva
    @29
    @38
    @15
    vt
    @31
    @29
    @32
    @31
    wcel
    #
    @38
    wa
    #
    wa
    #
    @32
    cK
    cnt
    cfv
    cfv
    #
    cK
    wcel
    #
    cB
    @54
    wcel
    #
    cF
    @54
    cC
    cin
    #
    cima
    #
    @5
    wss
    #
    @15
    @53
    @48
    @32
    cc
    wss
    #
    @55
    @49
    @53
    @48
    @51
    @60
    @49
    @29
    @51
    @38
    simprl
    #
    @9
    cK
    @32
    cc
    cc
    cK
    cK
    limcflf.k
    cnfldtopon
    #
    toponunii
    #
    neii1
    sylancr
    #
    @32
    cK
    cc
    @63
    ntropn
    sylancr
    @53
    @56
    @9
    @54
    wss
    #
    @53
    @51
    @65
    @61
    @53
    @48
    @9
    cc
    wss
    #
    @60
    @51
    @65
    wb
    @48
    @53
    @49
    a1i
    wph
    @66
    @4
    @28
    @52
    wph
    cB
    cc
    wph
    cA
    cK
    clp
    cfv
    cfv
    #
    cc
    cB
    wph
    @48
    cA
    cc
    wss
    @67
    cc
    wss
    @49
    limcflf.a
    cA
    cK
    cc
    @63
    lpss
    sylancr
    limcflf.b
    sseldd
    #
    snssd
    ad3antrrr
    @64
    @9
    cK
    @32
    cc
    @63
    neiint
    syl3anc
    mpbid
    @53
    cB
    cc
    wcel
    #
    @56
    @65
    wb
    wph
    @69
    @4
    @28
    @52
    @68
    ad3antrrr
    cB
    @54
    cc
    snssg
    syl
    mpbird
    @53
    @58
    @37
    @5
    @53
    @54
    @32
    wss
    #
    @57
    @33
    wss
    @58
    @37
    wss
    @53
    @48
    @60
    @70
    @49
    @64
    @32
    cK
    cc
    @63
    ntrss2
    sylancr
    @54
    @32
    cC
    ssrin
    @57
    @33
    cF
    imass2
    3syl
    @29
    @51
    @38
    simprr
    sstrd
    @14
    @56
    @59
    wa
    vw
    @54
    cK
    @7
    @54
    wceq
    #
    @8
    @56
    @13
    @59
    @7
    @54
    cB
    eleq2
    @71
    @12
    @58
    @5
    @71
    @11
    @57
    cF
    @71
    @11
    @7
    cC
    cin
    @57
    cC
    @10
    @7
    limcflf.c
    ineq2i
    @7
    @54
    cC
    ineq1
    syl5eqr
    imaeq2d
    sseq1d
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    impbid2
    3bitr4rd
    anassrs
    pm5.74da
    ralbidva
    pm5.32da
    wph
    vw
    vu
    cA
    cB
    @3
    cF
    cK
    limcflf.f
    limcflf.a
    @68
    limcflf.k
    ellimc2
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    #
    cL
    cC
    cfil
    cfv
    wcel
    cC
    cc
    @1
    wf
    #
    @25
    @24
    wb
    @72
    wph
    @62
    a1i
    wph
    cA
    cB
    cC
    cF
    cK
    cL
    limcflf.f
    limcflf.a
    limcflf.b
    limcflf.k
    limcflf.c
    limcflf.l
    limcflflem
    wph
    cA
    cc
    cF
    wf
    cC
    cA
    wss
    @73
    limcflf.f
    @45
    cA
    cc
    cC
    cF
    fssres
    sylancl
    @3
    vu
    @1
    cK
    cL
    cc
    cC
    vs
    isflf
    syl3anc
    3bitr4d
    eqrdv
end
