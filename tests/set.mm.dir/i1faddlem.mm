include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "crn.mm"
include "cv.mm"
include "cmin.mm"
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
include "ad2antrr.mm"
include "simprl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "simprr.mm"
include "eqidd.mm"
include "ofval.mm"
include "ad2ant2r.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "ffvelrnd.mm"
include "pncand.mm"
include "eqtr2d.mm"
include "mpbir2and.mm"
include "elind.mm"
include "oveq2.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "sneq.mm"
include "ineq12d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "elin.mm"
include "anbi12d.mm"
include "anandi.mm"
include "simprrl.mm"
include "simprrr.mm"
include "oveq12d.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "npcand.mm"
include "3eqtrd.mm"
include "jca.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "rexlimdvw.mm"
include "impbid.mm"
include "bitrd.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem i1faddlem
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
  assert |- ( ( ph /\ A e. CC ) -> ( `' ( F oF + G ) " { A } ) = U_ y e. ran G ( ( `' F " { ( A - y ) } ) i^i ( `' G " { y } ) ) )

  proof
    wph
    cA
    cc
    wcel
    #
    wa
    #
    vz
    cF
    cG
    caddc
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
    cF
    ccnv
    #
    cA
    vy
    cv
    #
    cmin
    co
    #
    csn
    #
    cima
    #
    cG
    ccnv
    #
    @6
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    @1
    vz
    cv
    #
    @3
    wcel
    #
    @15
    @13
    wcel
    #
    vy
    @4
    wrex
    #
    @15
    @14
    wcel
    @1
    @16
    @15
    cr
    wcel
    #
    @15
    @2
    cfv
    #
    cA
    wceq
    #
    wa
    #
    @18
    @1
    @2
    cr
    wfn
    #
    @16
    @22
    wb
    wph
    @23
    @0
    wph
    cr
    cr
    caddc
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
    @24
    i1fadd.1
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    ffn
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
    @26
    wcel
    @29
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
    wph
    reex
    a1i
    #
    @33
    cr
    inidm
    #
    offn
    adantr
    cr
    cA
    @15
    @2
    fniniseg
    syl
    @1
    @22
    @18
    @1
    @22
    @18
    @1
    @22
    wa
    #
    @15
    cG
    cfv
    #
    @4
    wcel
    #
    @15
    @5
    cA
    @36
    cmin
    co
    #
    csn
    #
    cima
    #
    @10
    @36
    csn
    #
    cima
    #
    cin
    #
    wcel
    #
    @18
    @35
    @30
    @19
    @37
    wph
    @30
    @0
    @22
    @32
    ad2antrr
    #
    @1
    @19
    @21
    simprl
    #
    cr
    @15
    cG
    fnfvelrn
    syl2anc
    @35
    @40
    @42
    @15
    @35
    @15
    @40
    wcel
    #
    @19
    @15
    cF
    cfv
    #
    @38
    wceq
    #
    @46
    @35
    @38
    @48
    @36
    caddc
    co
    #
    @36
    cmin
    co
    @48
    @35
    cA
    @50
    @36
    cmin
    @35
    @20
    cA
    @50
    @1
    @19
    @21
    simprr
    wph
    @19
    @20
    @50
    wceq
    #
    @0
    @21
    wph
    cr
    cr
    @48
    @36
    caddc
    cr
    cF
    cG
    cvv
    cvv
    @15
    @28
    @32
    @33
    @33
    @34
    wph
    @19
    wa
    #
    @48
    eqidd
    @52
    @36
    eqidd
    ofval
    #
    ad2ant2r
    eqtr3d
    oveq1d
    @35
    @48
    @36
    @35
    cr
    cc
    @15
    cF
    wph
    cr
    cc
    cF
    wf
    #
    @0
    @22
    wph
    @24
    cr
    cc
    wss
    #
    @54
    @27
    ax-resscn
    cr
    cr
    cc
    cF
    fss
    sylancl
    ad2antrr
    @46
    ffvelrnd
    @35
    cr
    cc
    @15
    cG
    wph
    cr
    cc
    cG
    wf
    #
    @0
    @22
    wph
    @29
    @55
    @56
    @31
    ax-resscn
    cr
    cr
    cc
    cG
    fss
    sylancl
    #
    ad2antrr
    @46
    ffvelrnd
    pncand
    eqtr2d
    @35
    @25
    @47
    @19
    @49
    wa
    wb
    wph
    @25
    @0
    @22
    @28
    ad2antrr
    cr
    @38
    @15
    cF
    fniniseg
    syl
    mpbir2and
    @35
    @15
    @42
    wcel
    #
    @19
    @36
    @36
    wceq
    #
    @46
    @35
    @36
    eqidd
    @35
    @30
    @58
    @19
    @59
    wa
    wb
    @45
    cr
    @36
    @15
    cG
    fniniseg
    syl
    mpbir2and
    elind
    @17
    @44
    vy
    @36
    @4
    @6
    @36
    wceq
    #
    @13
    @43
    @15
    @60
    @9
    @40
    @12
    @42
    @60
    @8
    @39
    @5
    @60
    @7
    @38
    @6
    @36
    cA
    cmin
    oveq2
    sneqd
    imaeq2d
    @60
    @11
    @41
    @10
    @6
    @36
    sneq
    imaeq2d
    ineq12d
    eleq2d
    rspcev
    syl2anc
    ex
    @1
    @17
    @22
    vy
    @4
    @17
    @15
    @9
    wcel
    #
    @15
    @12
    wcel
    #
    wa
    #
    @1
    @22
    @15
    @9
    @12
    elin
    @1
    @63
    @19
    @48
    @7
    wceq
    #
    wa
    #
    @19
    @36
    @6
    wceq
    #
    wa
    #
    wa
    #
    @22
    @1
    @61
    @65
    @62
    @67
    @1
    @25
    @61
    @65
    wb
    wph
    @25
    @0
    @28
    adantr
    cr
    @7
    @15
    cF
    fniniseg
    syl
    @1
    @30
    @62
    @67
    wb
    wph
    @30
    @0
    @32
    adantr
    cr
    @6
    @15
    cG
    fniniseg
    syl
    anbi12d
    @68
    @19
    @64
    @66
    wa
    #
    wa
    #
    @1
    @22
    @19
    @64
    @66
    anandi
    @1
    @70
    @22
    @1
    @70
    wa
    #
    @19
    @21
    @1
    @19
    @69
    simprl
    #
    @71
    @20
    @50
    @7
    @6
    caddc
    co
    cA
    wph
    @19
    @51
    @0
    @69
    @53
    ad2ant2r
    @71
    @48
    @7
    @36
    @6
    caddc
    @1
    @19
    @64
    @66
    simprrl
    @1
    @19
    @64
    @66
    simprrr
    #
    oveq12d
    @71
    cA
    @6
    wph
    @0
    @70
    simplr
    @71
    @36
    @6
    cc
    @73
    @71
    cr
    cc
    @15
    cG
    wph
    @56
    @0
    @70
    @57
    ad2antrr
    @72
    ffvelrnd
    eqeltrrd
    npcand
    3eqtrd
    jca
    ex
    syl5bir
    sylbid
    syl5bi
    rexlimdvw
    impbid
    bitrd
    vy
    @15
    @4
    @13
    eliun
    syl6bbr
    eqrdv
end
