include "cdomn.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cprime.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "wa.mm"
include "c2.mm"
include "cuz.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "cn.mm"
include "c1.mm"
include "cn0.mm"
include "csn.mm"
include "cdif.mm"
include "crg.mm"
include "domnring.mm"
include "eqid.mm"
include "chrcl.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dfn2.mm"
include "syl6eleqr.mm"
include "cnzr.mm"
include "domnnzr.mm"
include "wb.mm"
include "nzrring.mm"
include "chrnzr.mm"
include "ibi.mm"
include "eluz2b3.mm"
include "czrh.mm"
include "c0g.mm"
include "cmulr.mm"
include "zring.mm"
include "crh.mm"
include "ad2antrr.mm"
include "zrhrhm.mm"
include "simprl.mm"
include "simprr.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "cbs.mm"
include "simpll.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "domneq0.mm"
include "bitrd.mm"
include "biimpd.mm"
include "zmulcl.mm"
include "adantl.mm"
include "chrdvds.mm"
include "syl2anc.mm"
include "orbi12d.mm"
include "3imtr4d.mm"
include "ralrimivva.mm"
include "isprm6.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"

theorem domnchr
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. Domn -> ( ( chr ` R ) = 0 \/ ( chr ` R ) e. Prime ) )

  proof
    cR
    cdomn
    wcel
    #
    cR
    cchr
    cfv
    #
    cc0
    wceq
    #
    @1
    cprime
    wcel
    #
    @2
    wn
    @1
    cc0
    wne
    #
    @0
    @3
    @1
    cc0
    df-ne
    @0
    @4
    @3
    @0
    @4
    wa
    #
    @1
    c2
    cuz
    cfv
    wcel
    #
    @1
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @1
    @7
    cdvds
    wbr
    #
    @1
    @8
    cdvds
    wbr
    #
    wo
    #
    wi
    #
    vy
    cz
    wral
    vx
    cz
    wral
    @3
    @5
    @1
    cn
    wcel
    @1
    c1
    wne
    #
    @6
    @5
    @1
    cn0
    cc0
    csn
    cdif
    #
    cn
    @5
    @1
    cn0
    wcel
    #
    @4
    @1
    @16
    wcel
    @0
    @17
    @4
    @0
    cR
    crg
    wcel
    #
    @17
    cR
    domnring
    #
    @1
    cR
    @1
    eqid
    #
    chrcl
    syl
    adantr
    @0
    @4
    simpr
    @1
    cn0
    cc0
    eldifsn
    sylanbrc
    dfn2
    syl6eleqr
    @0
    @15
    @4
    @0
    cR
    cnzr
    wcel
    #
    @15
    cR
    domnnzr
    @21
    @15
    @21
    @18
    @21
    @15
    wb
    cR
    nzrring
    cR
    chrnzr
    syl
    ibi
    syl
    adantr
    @1
    eluz2b3
    sylanbrc
    @5
    @14
    vx
    vy
    cz
    cz
    @5
    @7
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    wa
    #
    wa
    #
    @9
    cR
    czrh
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    @7
    @26
    cfv
    #
    @28
    wceq
    #
    @8
    @26
    cfv
    #
    @28
    wceq
    #
    wo
    #
    @10
    @13
    @25
    @29
    @34
    @25
    @29
    @30
    @32
    cR
    cmulr
    cfv
    #
    co
    #
    @28
    wceq
    #
    @34
    @25
    @27
    @36
    @28
    @25
    @26
    zring
    cR
    crh
    co
    wcel
    #
    @22
    @23
    @27
    @36
    wceq
    @25
    @18
    @38
    @0
    @18
    @4
    @24
    @19
    ad2antrr
    #
    cR
    @26
    @26
    eqid
    #
    zrhrhm
    syl
    #
    @5
    @22
    @23
    simprl
    #
    @5
    @22
    @23
    simprr
    #
    @7
    @8
    zring
    cR
    cmul
    @35
    @26
    cz
    zringbas
    zringmulr
    @35
    eqid
    #
    rhmmul
    syl3anc
    eqeq1d
    @25
    @0
    @30
    cR
    cbs
    cfv
    #
    wcel
    @32
    @45
    wcel
    @37
    @34
    wb
    @0
    @4
    @24
    simpll
    @25
    cz
    @45
    @7
    @26
    @25
    @38
    cz
    @45
    @26
    wf
    @41
    cz
    @45
    zring
    cR
    @26
    zringbas
    @45
    eqid
    #
    rhmf
    syl
    #
    @42
    ffvelrnd
    @25
    cz
    @45
    @8
    @26
    @47
    @43
    ffvelrnd
    @45
    cR
    @35
    @30
    @32
    @28
    @46
    @44
    @28
    eqid
    #
    domneq0
    syl3anc
    bitrd
    biimpd
    @25
    @18
    @9
    cz
    wcel
    #
    @10
    @29
    wb
    @39
    @24
    @49
    @5
    @7
    @8
    zmulcl
    adantl
    @1
    cR
    @26
    @9
    @28
    @20
    @40
    @48
    chrdvds
    syl2anc
    @25
    @11
    @31
    @12
    @33
    @25
    @18
    @22
    @11
    @31
    wb
    @39
    @42
    @1
    cR
    @26
    @7
    @28
    @20
    @40
    @48
    chrdvds
    syl2anc
    @25
    @18
    @23
    @12
    @33
    wb
    @39
    @43
    @1
    cR
    @26
    @8
    @28
    @20
    @40
    @48
    chrdvds
    syl2anc
    orbi12d
    3imtr4d
    ralrimivva
    vx
    vy
    @1
    isprm6
    sylanbrc
    ex
    syl5bir
    orrd
end
