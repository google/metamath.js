include "cmfs.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cpm.mm"
include "msubff.mm"
include "wss.mm"
include "mapsspm.mm"
include "a1i.mm"
include "fssresd.mm"
include "wa.mm"
include "cmrsub.mm"
include "wfn.mm"
include "eqid.mm"
include "mrsubff.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "elmapi.mm"
include "ffn.mm"
include "3syl.mm"
include "simplrr.mm"
include "cmty.mm"
include "cop.mm"
include "c2nd.mm"
include "c1st.mm"
include "fveq1d.mm"
include "adantr.mm"
include "syl.mm"
include "ssid.mm"
include "cmtc.mm"
include "cxp.mm"
include "mtyf2.mm"
include "ad3antrrr.mm"
include "opelxpi.mm"
include "sylancom.mm"
include "mexval.mm"
include "syl6eleqr.mm"
include "msubval.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"
include "fvex.mm"
include "opth.mm"
include "simprbi.mm"
include "vex.mm"
include "op2nd.mm"
include "fveq2i.mm"
include "3eqtr3g.mm"
include "eqfnfvd.mm"
include "wb.mm"
include "mrsubff1.mm"
include "f1fveq.mm"
include "sylan.mm"
include "fvres.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "bitr3d.mm"
include "mpbird.mm"
include "expr.mm"
include "ralrimdva.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "3imtr4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem msubff1
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vv: setvar v
  assume msubff1.v: |- V = ( mVR ` T )
  assume msubff1.r: |- R = ( mREx ` T )
  assume msubff1.s: |- S = ( mSubst ` T )
  assume msubff1.e: |- E = ( mEx ` T )


  assert |- ( T e. mFS -> ( S |` ( R ^m V ) ) : ( R ^m V ) -1-1-> ( E ^m E ) )

  proof
    cT
    cmfs
    wcel
    #
    cR
    cV
    cmap
    co
    #
    cE
    cE
    cmap
    co
    #
    cS
    @1
    cres
    #
    wf
    vf
    cv
    #
    @3
    cfv
    #
    vg
    cv
    #
    @3
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vg
    @1
    wral
    vf
    @1
    wral
    @1
    @2
    @3
    wf1
    @0
    cR
    cV
    cpm
    co
    #
    @2
    @1
    cS
    cR
    cS
    cT
    cE
    cV
    cmfs
    msubff1.v
    msubff1.r
    msubff1.s
    msubff1.e
    msubff
    @1
    @11
    wss
    @0
    cR
    cV
    mapsspm
    #
    a1i
    fssresd
    @0
    @10
    vf
    vg
    @1
    @1
    @0
    @4
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    wa
    #
    @4
    cS
    cfv
    #
    @6
    cS
    cfv
    #
    wceq
    #
    vv
    cv
    #
    @4
    cfv
    @20
    @6
    cfv
    wceq
    #
    vv
    cV
    wral
    #
    @8
    @9
    @16
    @19
    @21
    vv
    cV
    @16
    @20
    cV
    wcel
    #
    @19
    @21
    @16
    @23
    @19
    wa
    #
    wa
    #
    @20
    @4
    @6
    @25
    @9
    @4
    cT
    cmrsub
    cfv
    #
    cfv
    #
    @6
    @26
    cfv
    #
    wceq
    #
    @25
    vr
    cR
    @27
    @28
    @25
    @27
    cR
    cR
    cmap
    co
    #
    wcel
    cR
    cR
    @27
    wf
    @27
    cR
    wfn
    @25
    @11
    @30
    @4
    @26
    @0
    @11
    @30
    @26
    wf
    @15
    @24
    cR
    @26
    cT
    cV
    cmfs
    msubff1.v
    msubff1.r
    @26
    eqid
    #
    mrsubff
    ad2antrr
    #
    @25
    @1
    @11
    @4
    @12
    @0
    @13
    @14
    @24
    simplrl
    #
    sseldi
    ffvelrnd
    @27
    cR
    cR
    elmapi
    cR
    cR
    @27
    ffn
    3syl
    @25
    @28
    @30
    wcel
    cR
    cR
    @28
    wf
    @28
    cR
    wfn
    @25
    @11
    @30
    @6
    @26
    @32
    @25
    @1
    @11
    @6
    @12
    @0
    @13
    @14
    @24
    simplrr
    #
    sseldi
    ffvelrnd
    @28
    cR
    cR
    elmapi
    cR
    cR
    @28
    ffn
    3syl
    @25
    vr
    cv
    #
    cR
    wcel
    #
    wa
    #
    @20
    cT
    cmty
    cfv
    #
    cfv
    #
    @35
    cop
    #
    c2nd
    cfv
    #
    @27
    cfv
    #
    @41
    @28
    cfv
    #
    @35
    @27
    cfv
    @35
    @28
    cfv
    @37
    @40
    c1st
    cfv
    #
    @42
    cop
    #
    @44
    @43
    cop
    #
    wceq
    #
    @42
    @43
    wceq
    #
    @37
    @40
    @17
    cfv
    #
    @40
    @18
    cfv
    #
    @45
    @46
    @37
    @40
    @17
    @18
    @16
    @23
    @19
    @36
    simplrr
    fveq1d
    @37
    cV
    cR
    @4
    wf
    #
    cV
    cV
    wss
    #
    @40
    cE
    wcel
    #
    @49
    @45
    wceq
    @37
    @13
    @51
    @25
    @13
    @36
    @33
    adantr
    @4
    cR
    cV
    elmapi
    #
    syl
    @52
    @37
    cV
    ssid
    a1i
    #
    @37
    @40
    cT
    cmtc
    cfv
    #
    cR
    cxp
    #
    cE
    @25
    @36
    @39
    @56
    wcel
    @40
    @57
    wcel
    @37
    cV
    @56
    @20
    @38
    @0
    cV
    @56
    @38
    wf
    @15
    @24
    @36
    cT
    @56
    cV
    @38
    msubff1.v
    @56
    eqid
    #
    @38
    eqid
    mtyf2
    ad3antrrr
    @16
    @23
    @19
    @36
    simplrl
    ffvelrnd
    @39
    @35
    @56
    cR
    opelxpi
    sylancom
    cR
    cT
    cE
    @56
    @58
    msubff1.e
    msubff1.r
    mexval
    syl6eleqr
    #
    cV
    cR
    cS
    cT
    cE
    @4
    @26
    cV
    @40
    msubff1.v
    msubff1.r
    msubff1.s
    msubff1.e
    @31
    msubval
    syl3anc
    @37
    cV
    cR
    @6
    wf
    #
    @52
    @53
    @50
    @46
    wceq
    @37
    @14
    @60
    @25
    @14
    @36
    @34
    adantr
    @6
    cR
    cV
    elmapi
    #
    syl
    @55
    @59
    cV
    cR
    cS
    cT
    cE
    @6
    @26
    cV
    @40
    msubff1.v
    msubff1.r
    msubff1.s
    msubff1.e
    @31
    msubval
    syl3anc
    3eqtr3d
    @47
    @44
    @44
    wceq
    @48
    @44
    @42
    @44
    @43
    @40
    c1st
    fvex
    @41
    @27
    fvex
    opth
    simprbi
    syl
    @41
    @35
    @27
    @39
    @35
    @20
    @38
    fvex
    vr
    vex
    op2nd
    #
    fveq2i
    @41
    @35
    @28
    @62
    fveq2i
    3eqtr3g
    eqfnfvd
    @16
    @9
    @29
    wb
    @24
    @16
    @4
    @26
    @1
    cres
    #
    cfv
    #
    @6
    @63
    cfv
    #
    wceq
    #
    @9
    @29
    @0
    @1
    @30
    @63
    wf1
    @15
    @66
    @9
    wb
    cR
    @26
    cT
    cV
    cmfs
    msubff1.v
    msubff1.r
    @31
    mrsubff1
    @1
    @30
    @4
    @6
    @63
    f1fveq
    sylan
    @15
    @66
    @29
    wb
    @0
    @13
    @14
    @64
    @27
    @65
    @28
    @4
    @1
    @26
    fvres
    @6
    @1
    @26
    fvres
    eqeqan12d
    adantl
    bitr3d
    adantr
    mpbird
    fveq1d
    expr
    ralrimdva
    @15
    @8
    @19
    wb
    @0
    @13
    @14
    @5
    @17
    @7
    @18
    @4
    @1
    cS
    fvres
    @6
    @1
    cS
    fvres
    eqeqan12d
    adantl
    @15
    @9
    @22
    wb
    #
    @0
    @13
    @51
    @60
    @67
    @14
    @54
    @61
    @51
    @4
    cV
    wfn
    @6
    cV
    wfn
    @67
    @60
    cV
    cR
    @4
    ffn
    cV
    cR
    @6
    ffn
    vv
    cV
    @4
    @6
    eqfnfv
    syl2an
    syl2an
    adantl
    3imtr4d
    ralrimivva
    vf
    vg
    @1
    @2
    @3
    dff13
    sylanbrc
end
