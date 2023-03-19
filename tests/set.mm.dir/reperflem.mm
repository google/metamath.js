include "crest.mm"
include "co.mm"
include "cperf.mm"
include "wcel.mm"
include "clp.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "wral.mm"
include "cc.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "cxmt.mm"
include "wb.mm"
include "cnxmet.mm"
include "sseli.mm"
include "cnfldtopn.mm"
include "neibl.mm"
include "sylancr.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "cr.mm"
include "ralrimiva.mm"
include "rpre.mm"
include "rehalfcld.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "sseldi.mm"
include "adantr.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "simpr.mm"
include "rphalfcld.mm"
include "rpcnd.mm"
include "pncan2d.mm"
include "fveq2d.mm"
include "rpred.mm"
include "rpge0d.mm"
include "absidd.mm"
include "3eqtrd.mm"
include "rphalflt.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "cxr.mm"
include "a1i.mm"
include "rpxr.mm"
include "elbl3.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "cc0.mm"
include "rpne0d.mm"
include "eqnetrd.mm"
include "subne0ad.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "inelcm.mm"
include "wi.mm"
include "ssrin.mm"
include "ssn0.mm"
include "ex.mm"
include "syl.mm"
include "syl5com.mm"
include "rexlimdva.mm"
include "adantld.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "islp2.mm"
include "mp3an12.mm"
include "ssriv.mm"
include "restperf.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem reperflem
  let vv: setvar v
  let vu: setvar u
  let cS: class S
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume recld2.1: |- J = ( TopOpen ` CCfld )
  assume reperflem.2: |- ( ( u e. S /\ v e. RR ) -> ( u + v ) e. S )
  assume reperflem.3: |- S C_ CC

  disjoint J u
  disjoint u v
  disjoint S u
  disjoint S v
  disjoint n r
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint J x
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint n v
  disjoint S n
  disjoint r v
  disjoint S r
  assert |- ( J |`t S ) e. Perf

  proof
    cJ
    cS
    crest
    co
    #
    cperf
    wcel
    #
    cS
    cS
    cJ
    clp
    cfv
    cfv
    #
    wss
    #
    vu
    cS
    @2
    vu
    cv
    #
    cS
    wcel
    #
    @4
    @2
    wcel
    #
    vn
    cv
    #
    cS
    @4
    csn
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    vn
    @8
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    @5
    @11
    vn
    @12
    @5
    @7
    @12
    wcel
    #
    @7
    cc
    wss
    #
    @4
    vr
    cv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    @7
    wss
    #
    vr
    crp
    wrex
    #
    wa
    #
    @11
    @5
    @17
    cc
    cxmt
    cfv
    wcel
    #
    @4
    cc
    wcel
    #
    @14
    @21
    wb
    cnxmet
    cS
    cc
    @4
    reperflem.3
    sseli
    #
    @17
    @4
    cJ
    @7
    cc
    vr
    cJ
    recld2.1
    cnfldtopn
    neibl
    sylancr
    @5
    @20
    @11
    @15
    @5
    @19
    @11
    vr
    crp
    @5
    @16
    crp
    wcel
    #
    wa
    #
    @18
    @9
    cin
    #
    c0
    wne
    #
    @19
    @11
    @26
    @4
    @16
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @18
    wcel
    #
    @30
    @9
    wcel
    #
    @28
    @26
    @31
    @30
    @4
    @17
    co
    #
    @16
    clt
    wbr
    #
    @26
    @33
    @29
    @16
    clt
    @26
    @33
    @30
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @29
    cabs
    cfv
    @29
    @26
    @30
    cc
    wcel
    #
    @23
    @33
    @36
    wceq
    @26
    cS
    cc
    @30
    reperflem.3
    @5
    @4
    vv
    cv
    #
    caddc
    co
    #
    cS
    wcel
    #
    vv
    cr
    wral
    @29
    cr
    wcel
    @30
    cS
    wcel
    #
    @25
    @5
    @40
    vv
    cr
    reperflem.2
    ralrimiva
    @25
    @16
    @16
    rpre
    rehalfcld
    @40
    @41
    vv
    @29
    cr
    @38
    @29
    wceq
    @39
    @30
    cS
    @38
    @29
    @4
    caddc
    oveq2
    eleq1d
    rspccva
    syl2an
    #
    sseldi
    #
    @5
    @23
    @25
    @24
    adantr
    #
    @30
    @4
    @17
    @17
    eqid
    cnmetdval
    syl2anc
    @26
    @35
    @29
    cabs
    @26
    @4
    @29
    @44
    @26
    @29
    @26
    @16
    @5
    @25
    simpr
    rphalfcld
    #
    rpcnd
    pncan2d
    #
    fveq2d
    @26
    @29
    @26
    @29
    @45
    rpred
    @26
    @29
    @45
    rpge0d
    absidd
    3eqtrd
    @25
    @29
    @16
    clt
    wbr
    @5
    @16
    rphalflt
    adantl
    eqbrtrd
    @26
    @22
    @16
    cxr
    wcel
    #
    @23
    @37
    @31
    @34
    wb
    @22
    @26
    cnxmet
    a1i
    @25
    @47
    @5
    @16
    rpxr
    adantl
    @44
    @43
    @30
    @17
    @4
    @16
    cc
    elbl3
    syl22anc
    mpbird
    @26
    @41
    @30
    @4
    wne
    @32
    @42
    @26
    @30
    @4
    @43
    @44
    @26
    @35
    @29
    cc0
    @46
    @26
    @29
    @45
    rpne0d
    eqnetrd
    subne0ad
    @30
    cS
    @4
    eldifsn
    sylanbrc
    @30
    @18
    @9
    inelcm
    syl2anc
    @19
    @27
    @10
    wss
    #
    @28
    @11
    wi
    @18
    @7
    @9
    ssrin
    @48
    @28
    @11
    @27
    @10
    ssn0
    ex
    syl
    syl5com
    rexlimdva
    adantld
    sylbid
    ralrimiv
    @5
    @23
    @6
    @13
    wb
    #
    @24
    cJ
    ctop
    wcel
    #
    cS
    cc
    wss
    #
    @23
    @49
    cJ
    recld2.1
    cnfldtop
    #
    reperflem.3
    @4
    cS
    vn
    cJ
    cc
    cc
    cJ
    cJ
    recld2.1
    cnfldtopon
    toponunii
    #
    islp2
    mp3an12
    syl
    mpbird
    ssriv
    @50
    @51
    @1
    @3
    wb
    @52
    reperflem.3
    cJ
    @0
    cc
    cS
    @53
    @0
    eqid
    restperf
    mp2an
    mpbir
end
