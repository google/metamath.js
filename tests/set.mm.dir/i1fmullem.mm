include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "crn.mm"
include "cv.mm"
include "cdiv.mm"
include "cin.mm"
include "ciun.mm"
include "wrex.mm"
include "cr.mm"
include "cfv.mm"
include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "cvv.mm"
include "wf.mm"
include "citg1.mm"
include "cdm.mm"
include "i1ff.mm"
include "syl.mm"
include "ffn.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "offn.mm"
include "adantr.mm"
include "fniniseg.mm"
include "eqidd.mm"
include "ofval.mm"
include "eqeq1d.mm"
include "pm5.32da.mm"
include "wne.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "mul01d.mm"
include "3netr4d.mm"
include "oveq2.mm"
include "necon3i.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "divcan4d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "mpbir2and.mm"
include "elin.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "sneq.mm"
include "ineq12d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "anbi12d.mm"
include "anandi.mm"
include "3bitr4g.mm"
include "wi.mm"
include "eldifi.mm"
include "wss.mm"
include "frn.mm"
include "sylib.mm"
include "simpld.mm"
include "sseldd.mm"
include "simprd.mm"
include "divcan1d.mm"
include "oveq12.mm"
include "syl5ibrcom.mm"
include "anassrs.mm"
include "imdistanda.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "3bitrd.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem i1fmullem
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vz: setvar z
  let cB: class B
  let vw: setvar w
  let cI: class I
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )

  disjoint A y
  disjoint F y
  disjoint G y
  disjoint ph y
  disjoint i j
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint y z
  disjoint A z
  disjoint B i
  disjoint B j
  disjoint w y
  disjoint I w
  disjoint I y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint x y
  disjoint x z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint F i
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint F j
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F z
  disjoint G i
  disjoint G j
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G z
  disjoint i ph
  disjoint j ph
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph z
  assert |- ( ( ph /\ A e. ( CC \ { 0 } ) ) -> ( `' ( F oF x. G ) " { A } ) = U_ y e. ( ran G \ { 0 } ) ( ( `' F " { ( A / y ) } ) i^i ( `' G " { y } ) ) )

  proof
    wph
    cA
    cc
    cc0
    csn
    #
    cdif
    wcel
    #
    wa
    #
    vz
    cF
    cG
    cmul
    cof
    co
    #
    ccnv
    cA
    csn
    cima
    #
    vy
    cG
    crn
    #
    @0
    cdif
    #
    cF
    ccnv
    #
    cA
    vy
    cv
    #
    cdiv
    co
    #
    csn
    #
    cima
    #
    cG
    ccnv
    #
    @8
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    @2
    vz
    cv
    #
    @4
    wcel
    #
    @17
    @15
    wcel
    #
    vy
    @6
    wrex
    #
    @17
    @16
    wcel
    @2
    @18
    @17
    cr
    wcel
    #
    @17
    @3
    cfv
    #
    cA
    wceq
    #
    wa
    #
    @21
    @17
    cF
    cfv
    #
    @17
    cG
    cfv
    #
    cmul
    co
    #
    cA
    wceq
    #
    wa
    #
    @20
    @2
    @3
    cr
    wfn
    #
    @18
    @24
    wb
    wph
    @30
    @1
    wph
    cr
    cr
    cmul
    cr
    cF
    cG
    cvv
    cvv
    wph
    cr
    cr
    cF
    wf
    #
    cF
    cr
    wfn
    #
    wph
    cF
    citg1
    cdm
    #
    wcel
    @31
    i1fadd.1
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    ffn
    #
    syl
    #
    wph
    cr
    cr
    cG
    wf
    #
    cG
    cr
    wfn
    #
    wph
    cG
    @33
    wcel
    @37
    i1fadd.2
    cG
    i1ff
    syl
    #
    cr
    cr
    cG
    ffn
    syl
    #
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    #
    @42
    cr
    inidm
    #
    offn
    adantr
    cr
    cA
    @17
    @3
    fniniseg
    syl
    @2
    @21
    @23
    @28
    @2
    @21
    wa
    #
    @22
    @27
    cA
    @2
    cr
    cr
    @25
    @26
    cmul
    cr
    cF
    cG
    cvv
    cvv
    @17
    wph
    @32
    @1
    @36
    adantr
    #
    wph
    @38
    @1
    @40
    adantr
    #
    @41
    @2
    reex
    a1i
    #
    @47
    @43
    @44
    @25
    eqidd
    @44
    @26
    eqidd
    ofval
    eqeq1d
    pm5.32da
    @2
    @29
    @20
    @2
    @29
    @20
    @2
    @29
    wa
    #
    @26
    @6
    wcel
    #
    @17
    @7
    cA
    @26
    cdiv
    co
    #
    csn
    #
    cima
    #
    @12
    @26
    csn
    #
    cima
    #
    cin
    #
    wcel
    #
    @20
    @48
    @26
    @5
    wcel
    #
    @26
    cc0
    wne
    #
    @49
    @48
    @38
    @21
    @57
    wph
    @38
    @1
    @29
    @40
    ad2antrr
    #
    @2
    @21
    @28
    simprl
    #
    cr
    @17
    cG
    fnfvelrn
    syl2anc
    @48
    @27
    @25
    cc0
    cmul
    co
    #
    wne
    @58
    @48
    cA
    cc0
    @27
    @61
    @1
    cA
    cc0
    wne
    wph
    @29
    cA
    cc
    cc0
    eldifsni
    ad2antlr
    @2
    @21
    @28
    simprr
    #
    @48
    @25
    @48
    @25
    @48
    cr
    cr
    @17
    cF
    wph
    @31
    @1
    @29
    @34
    ad2antrr
    #
    @60
    ffvelrnd
    recnd
    #
    mul01d
    3netr4d
    @26
    cc0
    @27
    @61
    @26
    cc0
    @25
    cmul
    oveq2
    necon3i
    syl
    #
    @26
    @5
    cc0
    eldifsn
    sylanbrc
    @48
    @17
    @52
    wcel
    #
    @17
    @54
    wcel
    #
    @56
    @48
    @66
    @21
    @25
    @50
    wceq
    #
    @60
    @48
    @27
    @26
    cdiv
    co
    @25
    @50
    @48
    @25
    @26
    @64
    @48
    @26
    @48
    cr
    cr
    @17
    cG
    wph
    @37
    @1
    @29
    @39
    ad2antrr
    @60
    ffvelrnd
    recnd
    @65
    divcan4d
    @48
    @27
    cA
    @26
    cdiv
    @62
    oveq1d
    eqtr3d
    @48
    @32
    @66
    @21
    @68
    wa
    wb
    @48
    @31
    @32
    @63
    @35
    syl
    cr
    @50
    @17
    cF
    fniniseg
    syl
    mpbir2and
    @48
    @67
    @21
    @26
    @26
    wceq
    #
    @60
    @48
    @26
    eqidd
    @48
    @38
    @67
    @21
    @69
    wa
    wb
    @59
    cr
    @26
    @17
    cG
    fniniseg
    syl
    mpbir2and
    @17
    @52
    @54
    elin
    sylanbrc
    @19
    @56
    vy
    @26
    @6
    @8
    @26
    wceq
    #
    @15
    @55
    @17
    @70
    @11
    @52
    @14
    @54
    @70
    @10
    @51
    @7
    @70
    @9
    @50
    @8
    @26
    cA
    cdiv
    oveq2
    sneqd
    imaeq2d
    @70
    @13
    @53
    @12
    @8
    @26
    sneq
    imaeq2d
    ineq12d
    eleq2d
    rspcev
    syl2anc
    ex
    @2
    @19
    @29
    vy
    @6
    @2
    @8
    @6
    wcel
    #
    wa
    #
    @19
    @21
    @25
    @9
    wceq
    #
    @26
    @8
    wceq
    #
    wa
    #
    wa
    #
    @29
    @2
    @19
    @76
    wb
    @71
    @2
    @17
    @11
    wcel
    #
    @17
    @14
    wcel
    #
    wa
    @21
    @73
    wa
    #
    @21
    @74
    wa
    #
    wa
    @19
    @76
    @2
    @77
    @79
    @78
    @80
    @2
    @32
    @77
    @79
    wb
    @45
    cr
    @9
    @17
    cF
    fniniseg
    syl
    @2
    @38
    @78
    @80
    wb
    @46
    cr
    @8
    @17
    cG
    fniniseg
    syl
    anbi12d
    @17
    @11
    @14
    elin
    @21
    @73
    @74
    anandi
    3bitr4g
    adantr
    @72
    @21
    @75
    @28
    @2
    @71
    @21
    @75
    @28
    wi
    @2
    @71
    @21
    wa
    #
    wa
    #
    @28
    @75
    @9
    @8
    cmul
    co
    #
    cA
    wceq
    @82
    cA
    @8
    @1
    cA
    cc
    wcel
    wph
    @81
    cA
    cc
    @0
    eldifi
    ad2antlr
    @82
    @8
    @82
    @5
    cr
    @8
    @82
    @37
    @5
    cr
    wss
    wph
    @37
    @1
    @81
    @39
    ad2antrr
    cr
    cr
    cG
    frn
    syl
    @82
    @8
    @5
    wcel
    #
    @8
    cc0
    wne
    #
    @82
    @71
    @84
    @85
    wa
    @2
    @71
    @21
    simprl
    @8
    @5
    cc0
    eldifsn
    sylib
    #
    simpld
    sseldd
    recnd
    @82
    @84
    @85
    @86
    simprd
    divcan1d
    @75
    @27
    @83
    cA
    @25
    @9
    @26
    @8
    cmul
    oveq12
    eqeq1d
    syl5ibrcom
    anassrs
    imdistanda
    sylbid
    rexlimdva
    impbid
    3bitrd
    vy
    @17
    @6
    @15
    eliun
    syl6bbr
    eqrdv
end
