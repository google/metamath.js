include "crn.mm"
include "wcel.mm"
include "cconcat.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cmvar.mm"
include "cmap.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wfun.mm"
include "cima.mm"
include "cvv.mm"
include "cpm.mm"
include "wf.mm"
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
include "eqid.mm"
include "mrsubff.mm"
include "ffun.mm"
include "3syl.mm"
include "mrsubrn.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "cmcn.mm"
include "cun.mm"
include "cfrmd.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "cplusg.mm"
include "cword.mm"
include "simprl.mm"
include "cmrex.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "mrexval.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "elmapi.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "s1cld.mm"
include "ifclda.mm"
include "fmptd.mm"
include "ccatco.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "fvex.mm"
include "unex.mm"
include "frmdmnd.mm"
include "mp1i.mm"
include "wrdco.mm"
include "cbs.mm"
include "frmdbas.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "gsumccat.mm"
include "gsumwcl.mm"
include "frmdadd.mm"
include "3eqtrd.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "ccatcl.mm"
include "eleqtrrd.mm"
include "mrsubval.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "ex.mm"
include "com23.mm"
include "rexlimiv.mm"
include "syl.mm"
include "3impib.mm"

theorem mrsubccat
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vr: setvar r
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let vw: setvar w
  let cV: class V
  let cW: class W
  assume mrsubccat.s: |- S = ( mRSubst ` T )
  assume mrsubccat.r: |- R = ( mREx ` T )


  assert |- ( ( F e. ran S /\ X e. R /\ Y e. R ) -> ( F ` ( X ++ Y ) ) = ( ( F ` X ) ++ ( F ` Y ) ) )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cX
    cR
    wcel
    #
    cY
    cR
    wcel
    #
    cX
    cY
    cconcat
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cconcat
    co
    #
    wceq
    #
    @1
    vf
    cv
    #
    cS
    cfv
    #
    cF
    wceq
    #
    vf
    cR
    cT
    cmvar
    cfv
    #
    cmap
    co
    #
    wrex
    #
    @2
    @3
    wa
    #
    @9
    wi
    #
    @1
    cS
    wfun
    #
    cF
    cS
    @14
    cima
    #
    wcel
    #
    @15
    @1
    cT
    cvv
    wcel
    #
    cR
    @13
    cpm
    co
    #
    cR
    cR
    cmap
    co
    #
    cS
    wf
    @18
    @1
    @0
    c0
    wceq
    @21
    @0
    cF
    n0i
    @21
    wn
    #
    @0
    c0
    crn
    c0
    @24
    cS
    c0
    @24
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubccat.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    cR
    cS
    cT
    @13
    cvv
    @13
    eqid
    #
    mrsubccat.r
    mrsubccat.s
    mrsubff
    @22
    @23
    cS
    ffun
    3syl
    @1
    @20
    @0
    @19
    cF
    cR
    cS
    cT
    @13
    @25
    mrsubccat.r
    mrsubccat.s
    mrsubrn
    eleq2i
    biimpi
    vf
    cF
    @14
    cS
    fvelima
    syl2anc
    @12
    @17
    vf
    @14
    @10
    @14
    wcel
    #
    @16
    @12
    @9
    @26
    @16
    @12
    @9
    wi
    @26
    @16
    wa
    #
    @4
    @11
    cfv
    #
    cX
    @11
    cfv
    #
    cY
    @11
    cfv
    #
    cconcat
    co
    #
    wceq
    @12
    @9
    @27
    cT
    cmcn
    cfv
    #
    @13
    cun
    #
    cfrmd
    cfv
    #
    vv
    @33
    vv
    cv
    #
    @13
    wcel
    #
    @35
    @10
    cfv
    #
    @35
    cs1
    #
    cif
    #
    cmpt
    #
    @4
    ccom
    #
    cgsu
    co
    #
    @34
    @40
    cX
    ccom
    #
    cgsu
    co
    #
    @34
    @40
    cY
    ccom
    #
    cgsu
    co
    #
    cconcat
    co
    #
    @28
    @31
    @27
    @42
    @34
    @43
    @45
    cconcat
    co
    #
    cgsu
    co
    #
    @44
    @46
    @34
    cplusg
    cfv
    #
    co
    #
    @47
    @27
    @41
    @48
    @34
    cgsu
    @27
    cX
    @33
    cword
    #
    wcel
    #
    cY
    @52
    wcel
    #
    @33
    @52
    @40
    wf
    #
    @41
    @48
    wceq
    @27
    cX
    cR
    @52
    @26
    @2
    @3
    simprl
    #
    @27
    @2
    @21
    cR
    @52
    wceq
    #
    @56
    @21
    cX
    cT
    cmrex
    cfv
    cR
    cX
    cT
    cmrex
    elfvex
    mrsubccat.r
    eleq2s
    @32
    cR
    cT
    @13
    cvv
    @32
    eqid
    #
    @25
    mrsubccat.r
    mrexval
    3syl
    #
    eleqtrd
    #
    @27
    cY
    cR
    @52
    @26
    @2
    @3
    simprr
    #
    @59
    eleqtrd
    #
    @27
    vv
    @33
    @39
    @52
    @40
    @27
    @35
    @33
    wcel
    #
    wa
    #
    @36
    @37
    @38
    @52
    @64
    @36
    wa
    @37
    cR
    @52
    @64
    @13
    cR
    @35
    @10
    @27
    @13
    cR
    @10
    wf
    #
    @63
    @26
    @65
    @16
    @10
    cR
    @13
    elmapi
    adantr
    #
    adantr
    ffvelrnda
    @27
    @57
    @63
    @36
    @59
    ad2antrr
    eleqtrd
    @64
    @36
    wn
    #
    wa
    @35
    @33
    @27
    @63
    @67
    simplr
    s1cld
    ifclda
    @40
    eqid
    fmptd
    #
    @33
    @52
    cX
    cY
    @40
    ccatco
    syl3anc
    oveq2d
    @27
    @34
    cmnd
    wcel
    #
    @43
    @52
    cword
    #
    wcel
    #
    @45
    @70
    wcel
    #
    @49
    @51
    wceq
    @33
    cvv
    wcel
    #
    @69
    @27
    @32
    @13
    cT
    cmcn
    fvex
    cT
    cmvar
    fvex
    unex
    #
    @33
    @34
    cvv
    @34
    eqid
    #
    frmdmnd
    mp1i
    #
    @27
    @53
    @55
    @71
    @60
    @68
    @33
    @52
    @40
    cX
    wrdco
    syl2anc
    #
    @27
    @54
    @55
    @72
    @62
    @68
    @33
    @52
    @40
    cY
    wrdco
    syl2anc
    #
    @52
    @50
    @34
    @43
    @45
    @34
    cbs
    cfv
    #
    @52
    @73
    @79
    @52
    wceq
    @74
    @79
    @33
    @34
    cvv
    @75
    @79
    eqid
    frmdbas
    ax-mp
    eqcomi
    #
    @50
    eqid
    #
    gsumccat
    syl3anc
    @27
    @44
    @52
    wcel
    #
    @46
    @52
    wcel
    #
    @51
    @47
    wceq
    @27
    @69
    @71
    @82
    @76
    @77
    @52
    @34
    @43
    @80
    gsumwcl
    syl2anc
    @27
    @69
    @72
    @83
    @76
    @78
    @52
    @34
    @45
    @80
    gsumwcl
    syl2anc
    @52
    @50
    @33
    @34
    @44
    @46
    @75
    @80
    @81
    frmdadd
    syl2anc
    3eqtrd
    @27
    @65
    @13
    @13
    wss
    #
    @4
    cR
    wcel
    @28
    @42
    wceq
    @66
    @84
    @27
    @13
    ssid
    a1i
    #
    @27
    @4
    @52
    cR
    @27
    @53
    @54
    @4
    @52
    wcel
    @60
    @62
    @33
    cX
    cY
    ccatcl
    syl2anc
    @59
    eleqtrrd
    vv
    @13
    @32
    cR
    cS
    cT
    @10
    @34
    @13
    @4
    @58
    @25
    mrsubccat.r
    mrsubccat.s
    @75
    mrsubval
    syl3anc
    @27
    @29
    @44
    @30
    @46
    cconcat
    @27
    @65
    @84
    @2
    @29
    @44
    wceq
    @66
    @85
    @56
    vv
    @13
    @32
    cR
    cS
    cT
    @10
    @34
    @13
    cX
    @58
    @25
    mrsubccat.r
    mrsubccat.s
    @75
    mrsubval
    syl3anc
    @27
    @65
    @84
    @3
    @30
    @46
    wceq
    @66
    @85
    @61
    vv
    @13
    @32
    cR
    cS
    cT
    @10
    @34
    @13
    cY
    @58
    @25
    mrsubccat.r
    mrsubccat.s
    @75
    mrsubval
    syl3anc
    oveq12d
    3eqtr4d
    @12
    @28
    @5
    @31
    @8
    @4
    @11
    cF
    fveq1
    @12
    @29
    @6
    @30
    @7
    cconcat
    cX
    @11
    cF
    fveq1
    cY
    @11
    cF
    fveq1
    oveq12d
    eqeq12d
    syl5ibcom
    ex
    com23
    rexlimiv
    syl
    3impib
end
