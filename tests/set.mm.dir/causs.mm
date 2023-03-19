include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "wa.mm"
include "crn.mm"
include "cin.mm"
include "wss.mm"
include "cca.mm"
include "cxp.mm"
include "cres.mm"
include "cc.mm"
include "wfun.mm"
include "cpm.mm"
include "co.mm"
include "caufpm.mm"
include "cdm.mm"
include "cvv.mm"
include "wb.mm"
include "elfvdm.mm"
include "cnex.mm"
include "elpmg.mm"
include "sylancl.mm"
include "biimpa.mm"
include "syldan.mm"
include "simprd.mm"
include "rnss.mm"
include "syl.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "adantlr.mm"
include "frn.mm"
include "ad2antlr.mm"
include "ssind.mm"
include "ex.mm"
include "wi.mm"
include "xmetres.mm"
include "sylan.mm"
include "inex1g.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "df-f.mm"
include "simplbi2.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "inss2.mm"
include "a1i.mm"
include "fss.mm"
include "sylan2.mm"
include "ancoms.mm"
include "ffvelrn.mm"
include "eluznn.mm"
include "anassrs.mm"
include "ovresd.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqidd.mm"
include "simpr.mm"
include "iscauf.mm"
include "simpl.mm"
include "id.mm"
include "inss1.mm"
include "syl2anr.mm"
include "3bitr4rd.mm"
include "sylan9r.mm"
include "pm5.21ndd.mm"

theorem causs
  let cD: class D
  let cF: class F
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( *Met ` X ) /\ F : NN --> Y ) -> ( F e. ( Cau ` D ) <-> F e. ( Cau ` ( D |` ( Y X. Y ) ) ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cn
    cY
    cF
    wf
    #
    wa
    #
    cF
    crn
    #
    cX
    cY
    cin
    #
    wss
    #
    cF
    cD
    cca
    cfv
    wcel
    #
    cF
    cD
    cY
    cY
    cxp
    cres
    #
    cca
    cfv
    wcel
    #
    @2
    @6
    @5
    @2
    @6
    wa
    @3
    cX
    cY
    @0
    @6
    @3
    cX
    wss
    @1
    @0
    @6
    wa
    #
    @3
    cc
    cX
    cxp
    #
    crn
    #
    cX
    @9
    cF
    @10
    wss
    #
    @3
    @11
    wss
    @9
    cF
    wfun
    #
    @12
    @0
    @6
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @13
    @12
    wa
    #
    cD
    cF
    cX
    caufpm
    @0
    @14
    @15
    @0
    cX
    cxmt
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    #
    @14
    @15
    wb
    cD
    cX
    cxmt
    elfvdm
    #
    cnex
    cX
    cc
    cF
    @16
    cvv
    elpmg
    sylancl
    biimpa
    syldan
    simprd
    cF
    @10
    rnss
    syl
    cc
    cX
    rnxpss
    syl6ss
    adantlr
    @1
    @3
    cY
    wss
    @0
    @6
    cn
    cY
    cF
    frn
    ad2antlr
    ssind
    ex
    @0
    @8
    @5
    wi
    @1
    @0
    @8
    @5
    @0
    @8
    wa
    #
    @3
    cc
    @4
    cxp
    #
    crn
    #
    @4
    @20
    cF
    @21
    wss
    #
    @3
    @22
    wss
    @20
    @13
    @23
    @0
    @8
    cF
    @4
    cc
    cpm
    co
    wcel
    #
    @13
    @23
    wa
    #
    @0
    @7
    @4
    cxmt
    cfv
    wcel
    #
    @8
    @24
    cD
    cY
    cX
    xmetres
    #
    @7
    cF
    @4
    caufpm
    sylan
    @0
    @24
    @25
    @0
    @4
    cvv
    wcel
    #
    @18
    @24
    @25
    wb
    @0
    @17
    @28
    @19
    cX
    cY
    @16
    inex1g
    syl
    cnex
    @4
    cc
    cF
    cvv
    cvv
    elpmg
    sylancl
    biimpa
    syldan
    simprd
    cF
    @21
    rnss
    syl
    cc
    @4
    rnxpss
    syl6ss
    ex
    adantr
    @1
    @5
    cn
    @4
    cF
    wf
    #
    @0
    @6
    @8
    wb
    #
    @1
    cF
    cn
    wfn
    #
    @5
    @29
    wi
    cn
    cY
    cF
    ffn
    @29
    @31
    @5
    cn
    @4
    cF
    df-f
    simplbi2
    syl
    @0
    @29
    @30
    @0
    @29
    wa
    #
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    @7
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    @33
    cuz
    cfv
    #
    wral
    #
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    #
    @34
    @36
    cD
    co
    #
    @38
    clt
    wbr
    #
    vz
    @40
    wral
    #
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    #
    @8
    @6
    @32
    @1
    @43
    @48
    wb
    @29
    @0
    @1
    @0
    @29
    @4
    cY
    wss
    #
    @1
    @49
    @0
    cX
    cY
    inss2
    a1i
    cn
    @4
    cY
    cF
    fss
    sylan2
    ancoms
    @1
    @42
    @47
    vx
    crp
    @1
    @41
    @46
    vy
    cn
    @1
    @33
    cn
    wcel
    #
    wa
    #
    @39
    @45
    vz
    @40
    @51
    @35
    @40
    wcel
    #
    wa
    #
    @37
    @44
    @38
    clt
    @53
    @34
    @36
    cD
    cY
    @51
    @34
    cY
    wcel
    @52
    cn
    cY
    @33
    cF
    ffvelrn
    adantr
    @1
    @50
    @52
    @36
    cY
    wcel
    #
    @50
    @52
    wa
    @1
    @35
    cn
    wcel
    #
    @54
    @35
    @33
    eluznn
    cn
    cY
    @35
    cF
    ffvelrn
    sylan2
    anassrs
    ovresd
    breq1d
    ralbidva
    rexbidva
    ralbidv
    syl
    @32
    vx
    @36
    @34
    @7
    vy
    vz
    cF
    c1
    @4
    cn
    nnuz
    @0
    @26
    @29
    @27
    adantr
    @32
    1zzd
    #
    @32
    @55
    wa
    @36
    eqidd
    #
    @32
    @50
    wa
    @34
    eqidd
    #
    @0
    @29
    simpr
    iscauf
    @32
    vx
    @36
    @34
    cD
    vy
    vz
    cF
    c1
    cX
    cn
    nnuz
    @0
    @29
    simpl
    @56
    @57
    @58
    @29
    @29
    @4
    cX
    wss
    #
    cn
    cX
    cF
    wf
    @0
    @29
    id
    @59
    @0
    cX
    cY
    inss1
    a1i
    cn
    @4
    cX
    cF
    fss
    syl2anr
    iscauf
    3bitr4rd
    ex
    sylan9r
    pm5.21ndd
end
