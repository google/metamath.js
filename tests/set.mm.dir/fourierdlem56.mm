include "cr.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cdv.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "c1.mm"
include "cmul.mm"
include "ccos.mm"
include "cmin.mm"
include "cexp.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cif.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "cvv.mm"
include "csn.mm"
include "difss2d.mm"
include "sselda.mm"
include "1ex.mm"
include "ovex.mm"
include "ifex.mm"
include "a1i.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "elioore.mm"
include "adantl.mm"
include "recnd.mm"
include "halfcld.mm"
include "sincld.mm"
include "2cnd.mm"
include "wne.mm"
include "fourierdlem44.mm"
include "2ne0.mm"
include "divdiv1d.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "divcld.mm"
include "1red.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "remulcld.mm"
include "recoscld.mm"
include "resubcld.mm"
include "resqcld.mm"
include "cz.mm"
include "2z.mm"
include "expne0d.mm"
include "redivcld.mm"
include "1cnd.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "recn.mm"
include "dvmptid.mm"
include "wss.mm"
include "ioossre.mm"
include "eqid.mm"
include "tgioo2.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "wn.mm"
include "elsni.mm"
include "necon3ai.mm"
include "syl.mm"
include "eldifd.mm"
include "coscld.mm"
include "mulcld.mm"
include "cnelprrecn.mm"
include "wf.mm"
include "sinf.mm"
include "ffvelrnda.mm"
include "cosf.mm"
include "dvmptdivc.mm"
include "wfn.mm"
include "ffn.mm"
include "ax-mp.mm"
include "dffn5.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "dvsin.mm"
include "3eqtri.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "dvmptdiv.mm"
include "mulid2d.mm"
include "divrecd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq2ia.mm"

theorem fourierdlem56
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cK: class K
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem56.k: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )
  assume fourierdlem56.a: |- ( ph -> ( A (,) B ) C_ ( ( -u _pi [,] _pi ) \ { 0 } ) )
  assume fourierdlem56.r4: |- ( ( ph /\ s e. ( A (,) B ) ) -> s =/= 0 )

  disjoint A s
  disjoint B s
  disjoint ph s
  disjoint ph x
  disjoint s x
  disjoint k x
  assert |- ( ph -> ( RR _D ( s e. ( A (,) B ) |-> ( K ` s ) ) ) = ( s e. ( A (,) B ) |-> ( ( ( ( sin ` ( s / 2 ) ) - ( ( ( cos ` ( s / 2 ) ) / 2 ) x. s ) ) / ( ( sin ` ( s / 2 ) ) ^ 2 ) ) / 2 ) ) )

  proof
    wph
    cr
    vs
    cA
    cB
    cioo
    co
    #
    vs
    cv
    #
    cK
    cfv
    #
    cmpt
    #
    cdv
    co
    cr
    vs
    @0
    @1
    @1
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    vs
    @0
    c1
    @5
    cmul
    co
    #
    @4
    ccos
    cfv
    #
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @1
    cmul
    co
    #
    cmin
    co
    #
    @5
    c2
    cexp
    co
    #
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cmpt
    #
    vs
    @0
    @5
    @10
    c2
    cdiv
    co
    #
    @1
    cmul
    co
    #
    cmin
    co
    #
    @15
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cmpt
    #
    wph
    @3
    @8
    cr
    cdv
    wph
    vs
    @0
    @2
    @7
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    @1
    cc0
    wceq
    #
    c1
    @1
    c2
    @5
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    @29
    @7
    @26
    @1
    cpi
    cneg
    cpi
    cicc
    co
    #
    wcel
    #
    @30
    cvv
    wcel
    #
    @2
    @30
    wceq
    wph
    @0
    @31
    @1
    wph
    @0
    @31
    cc0
    csn
    #
    fourierdlem56.a
    difss2d
    sselda
    #
    @33
    @26
    @27
    c1
    @29
    1ex
    @1
    @28
    cdiv
    ovex
    ifex
    a1i
    vs
    @31
    @30
    cvv
    cK
    fourierdlem56.k
    fvmpt2
    syl2anc
    @26
    @27
    c1
    @29
    @26
    @1
    cc0
    fourierdlem56.r4
    neneqd
    iffalsed
    @26
    @7
    @1
    @5
    c2
    cmul
    co
    #
    cdiv
    co
    @29
    @26
    @1
    @5
    c2
    @26
    @1
    @25
    @1
    cr
    wcel
    #
    wph
    @1
    cA
    cB
    elioore
    #
    adantl
    #
    recnd
    #
    @26
    @4
    @26
    @1
    @40
    halfcld
    #
    sincld
    #
    @26
    2cnd
    #
    @26
    @32
    @1
    cc0
    wne
    @5
    cc0
    wne
    #
    @35
    fourierdlem56.r4
    @1
    fourierdlem44
    syl2anc
    #
    c2
    cc0
    wne
    #
    @26
    2ne0
    a1i
    divdiv1d
    @26
    @36
    @28
    @1
    cdiv
    @26
    @5
    c2
    @42
    @43
    mulcomd
    oveq2d
    eqtr2d
    3eqtrd
    mpteq2dva
    oveq2d
    wph
    vs
    @6
    @16
    c2
    cr
    cr
    @0
    cr
    cr
    cc
    cpr
    #
    wcel
    wph
    reelprrecn
    a1i
    #
    @26
    @1
    @5
    @40
    @42
    @45
    divcld
    @26
    @14
    @15
    @26
    @9
    @13
    @26
    c1
    @5
    @26
    1red
    #
    @26
    @4
    @26
    @1
    @39
    rehalfcld
    #
    resincld
    #
    remulcld
    @26
    @12
    @1
    @26
    @10
    @11
    @26
    @4
    @50
    recoscld
    @26
    c1
    @49
    rehalfcld
    #
    remulcld
    @39
    remulcld
    resubcld
    @26
    @5
    @51
    resqcld
    @26
    @5
    c2
    @42
    @45
    c2
    cz
    wcel
    @26
    2z
    a1i
    expne0d
    redivcld
    wph
    vs
    @1
    c1
    @5
    @12
    cr
    cc
    @0
    @48
    @40
    @26
    1cnd
    #
    wph
    vs
    @1
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
    @0
    @48
    @37
    @1
    cc
    wcel
    wph
    @1
    recn
    adantl
    wph
    @37
    wa
    1red
    wph
    vs
    cr
    @48
    dvmptid
    @0
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    @55
    @55
    eqid
    #
    tgioo2
    @56
    @0
    @54
    wcel
    wph
    cA
    cB
    iooretop
    a1i
    dvmptres
    #
    @26
    @5
    cc
    @34
    @42
    @26
    @44
    @5
    @34
    wcel
    #
    wn
    @45
    @58
    @5
    cc0
    @5
    cc0
    elsni
    necon3ai
    syl
    eldifd
    @26
    @10
    @11
    @26
    @4
    @41
    coscld
    @26
    c1
    @53
    halfcld
    mulcld
    wph
    vs
    vx
    @4
    @11
    vx
    cv
    #
    csin
    cfv
    #
    @59
    ccos
    cfv
    #
    cr
    cc
    @5
    @10
    cr
    cc
    @0
    cc
    @48
    cc
    @47
    wcel
    wph
    cnelprrecn
    a1i
    @41
    @52
    wph
    cc
    cc
    @59
    csin
    cc
    cc
    csin
    wf
    #
    wph
    sinf
    a1i
    ffvelrnda
    wph
    cc
    cc
    @59
    ccos
    cc
    cc
    ccos
    wf
    #
    wph
    cosf
    a1i
    ffvelrnda
    wph
    vs
    @1
    c1
    c2
    cr
    cr
    @0
    @48
    @40
    @49
    @57
    wph
    2cnd
    #
    @46
    wph
    2ne0
    a1i
    #
    dvmptdivc
    cc
    vx
    cc
    @60
    cmpt
    #
    cdv
    co
    #
    vx
    cc
    @61
    cmpt
    #
    wceq
    wph
    @67
    cc
    csin
    cdv
    co
    ccos
    @68
    @66
    csin
    cc
    cdv
    csin
    @66
    csin
    cc
    wfn
    #
    csin
    @66
    wceq
    @62
    @69
    sinf
    cc
    cc
    csin
    ffn
    ax-mp
    vx
    cc
    csin
    dffn5
    mpbi
    eqcomi
    oveq2i
    dvsin
    ccos
    cc
    wfn
    #
    ccos
    @68
    wceq
    @63
    @70
    cosf
    cc
    cc
    ccos
    ffn
    ax-mp
    vx
    cc
    ccos
    dffn5
    mpbi
    3eqtri
    a1i
    @59
    @4
    csin
    fveq2
    @59
    @4
    ccos
    fveq2
    dvmptco
    dvmptdiv
    @64
    @65
    dvmptdivc
    @18
    @24
    wceq
    wph
    vs
    @0
    @17
    @23
    @25
    @16
    @22
    c2
    cdiv
    @25
    @14
    @21
    @15
    cdiv
    @25
    @9
    @5
    @13
    @20
    cmin
    @25
    @5
    @25
    @4
    @25
    @1
    @25
    @1
    @38
    recnd
    halfcld
    #
    sincld
    mulid2d
    @25
    @12
    @19
    @1
    cmul
    @25
    @19
    @12
    @25
    @10
    c2
    @25
    @4
    @71
    coscld
    @25
    2cnd
    @46
    @25
    2ne0
    a1i
    divrecd
    eqcomd
    oveq1d
    oveq12d
    oveq1d
    oveq1d
    mpteq2ia
    a1i
    3eqtrd
end
