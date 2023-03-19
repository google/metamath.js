include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cmrex.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cs1.mm"
include "wceq.mm"
include "cmcn.mm"
include "cmvar.mm"
include "cdif.mm"
include "wral.mm"
include "cconcat.mm"
include "co.mm"
include "eqid.mm"
include "mrsubf.mm"
include "adantr.mm"
include "adantl.mm"
include "fco.mm"
include "syl2anc.mm"
include "cun.mm"
include "cword.mm"
include "eldifi.mm"
include "elun1.mm"
include "syl.mm"
include "s1cld.mm"
include "cvv.mm"
include "c0.mm"
include "n0i.mm"
include "wn.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "mrexval.mm"
include "eleqtrrd.mm"
include "fvco3.mm"
include "mrsubcn.mm"
include "adantll.mm"
include "fveq2d.mm"
include "adantlr.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "mrsubccat.mm"
include "3expb.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "ccatcl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wb.mm"
include "elmrsubrn.mm"
include "mpbir3and.mm"

theorem mrsubco
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cX: class X
  assume mrsubco.s: |- S = ( mRSubst ` T )


  assert |- ( ( F e. ran S /\ G e. ran S ) -> ( F o. G ) e. ran S )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    ccom
    #
    @0
    wcel
    #
    cT
    cmrex
    cfv
    #
    @6
    @4
    wf
    #
    vc
    cv
    #
    cs1
    #
    @4
    cfv
    #
    @9
    wceq
    #
    vc
    cT
    cmcn
    cfv
    #
    cT
    cmvar
    cfv
    #
    cdif
    #
    wral
    #
    vx
    cv
    #
    vy
    cv
    #
    cconcat
    co
    #
    @4
    cfv
    #
    @16
    @4
    cfv
    #
    @17
    @4
    cfv
    #
    cconcat
    co
    #
    wceq
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    @3
    @6
    @6
    cF
    wf
    #
    @6
    @6
    cG
    wf
    #
    @7
    @1
    @25
    @2
    @6
    cS
    cT
    cF
    mrsubco.s
    @6
    eqid
    #
    mrsubf
    adantr
    @2
    @26
    @1
    @6
    cS
    cT
    cG
    mrsubco.s
    @27
    mrsubf
    adantl
    #
    @6
    @6
    @6
    cF
    cG
    fco
    syl2anc
    @3
    @11
    vc
    @14
    @3
    @8
    @14
    wcel
    #
    wa
    #
    @10
    @9
    cG
    cfv
    #
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    @9
    @30
    @26
    @9
    @6
    wcel
    @10
    @32
    wceq
    @3
    @26
    @29
    @28
    adantr
    @30
    @9
    @12
    @13
    cun
    #
    cword
    #
    @6
    @30
    @8
    @34
    @29
    @8
    @34
    wcel
    #
    @3
    @29
    @8
    @12
    wcel
    @36
    @8
    @12
    @13
    eldifi
    @8
    @12
    @13
    elun1
    syl
    adantl
    s1cld
    @30
    cT
    cvv
    wcel
    #
    @6
    @35
    wceq
    #
    @3
    @37
    @29
    @1
    @37
    @2
    @1
    @0
    c0
    wceq
    @37
    @0
    cF
    n0i
    @37
    wn
    #
    @0
    c0
    crn
    c0
    @39
    cS
    c0
    @39
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubco.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    adantr
    #
    adantr
    @12
    @6
    cT
    @13
    cvv
    @12
    eqid
    #
    @13
    eqid
    #
    @27
    mrexval
    #
    syl
    eleqtrrd
    @6
    @6
    @9
    cF
    cG
    fvco3
    syl2anc
    @30
    @31
    @9
    cF
    @2
    @29
    @31
    @9
    wceq
    @1
    @12
    @6
    cS
    cT
    cG
    @13
    @8
    mrsubco.s
    @27
    @42
    @41
    mrsubcn
    adantll
    fveq2d
    @1
    @29
    @33
    @9
    wceq
    @2
    @12
    @6
    cS
    cT
    cF
    @13
    @8
    mrsubco.s
    @27
    @42
    @41
    mrsubcn
    adantlr
    3eqtrd
    ralrimiva
    @3
    @23
    vx
    vy
    @6
    @6
    @3
    @16
    @6
    wcel
    #
    @17
    @6
    wcel
    #
    wa
    #
    wa
    #
    @18
    cG
    cfv
    #
    cF
    cfv
    #
    @16
    cG
    cfv
    #
    cF
    cfv
    #
    @17
    cG
    cfv
    #
    cF
    cfv
    #
    cconcat
    co
    #
    @19
    @22
    @47
    @49
    @50
    @52
    cconcat
    co
    #
    cF
    cfv
    #
    @54
    @47
    @48
    @55
    cF
    @2
    @46
    @48
    @55
    wceq
    #
    @1
    @2
    @44
    @45
    @57
    @6
    cS
    cT
    cG
    @16
    @17
    mrsubco.s
    @27
    mrsubccat
    3expb
    adantll
    fveq2d
    @47
    @1
    @50
    @6
    wcel
    @52
    @6
    wcel
    @56
    @54
    wceq
    @1
    @2
    @46
    simpll
    @47
    @6
    @6
    @16
    cG
    @3
    @26
    @46
    @28
    adantr
    #
    @3
    @44
    @45
    simprl
    #
    ffvelrnd
    @47
    @6
    @6
    @17
    cG
    @58
    @3
    @44
    @45
    simprr
    #
    ffvelrnd
    @6
    cS
    cT
    cF
    @50
    @52
    mrsubco.s
    @27
    mrsubccat
    syl3anc
    eqtrd
    @47
    @26
    @18
    @6
    wcel
    @19
    @49
    wceq
    @58
    @47
    @18
    @35
    @6
    @47
    @16
    @35
    wcel
    @17
    @35
    wcel
    @18
    @35
    wcel
    @47
    @16
    @6
    @35
    @59
    @3
    @38
    @46
    @3
    @37
    @38
    @40
    @43
    syl
    adantr
    #
    eleqtrd
    @47
    @17
    @6
    @35
    @60
    @61
    eleqtrd
    @34
    @16
    @17
    ccatcl
    syl2anc
    @61
    eleqtrrd
    @6
    @6
    @18
    cF
    cG
    fvco3
    syl2anc
    @47
    @20
    @51
    @21
    @53
    cconcat
    @47
    @26
    @44
    @20
    @51
    wceq
    @58
    @59
    @6
    @6
    @16
    cF
    cG
    fvco3
    syl2anc
    @47
    @26
    @45
    @21
    @53
    wceq
    @58
    @60
    @6
    @6
    @17
    cF
    cG
    fvco3
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    @3
    @37
    @5
    @7
    @15
    @24
    w3a
    wb
    @40
    vx
    vy
    @12
    @6
    cS
    cT
    @4
    @13
    cvv
    vc
    mrsubco.s
    @27
    @42
    @41
    elmrsubrn
    syl
    mpbir3and
end
