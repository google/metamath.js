include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "crab.mm"
include "ciun.mm"
include "wceq.mm"
include "cun.mm"
include "wrex.mm"
include "iunrab.mm"
include "a1i.mm"
include "uneq1d.mm"
include "wo.mm"
include "unrab.mm"
include "wi.mm"
include "simpl.mm"
include "rexlimivw.mm"
include "snidg.mm"
include "ad2antlr.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "cedg.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "adantr.mm"
include "iedgedg.mm"
include "sylan.mm"
include "cpr.mm"
include "eqid.mm"
include "upgredg.mm"
include "ex.mm"
include "ad2antrr.mm"
include "w3a.mm"
include "dfsn2.mm"
include "eqcomi.mm"
include "elsni.mm"
include "sneq.mm"
include "eqcomd.mm"
include "syl5eq.mm"
include "eleq2s.mm"
include "preq2.mm"
include "eleq2d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "imp.mm"
include "olcd.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "com12.mm"
include "wne.mm"
include "simpr3.mm"
include "necomd.mm"
include "simpr2.mm"
include "prproe.mm"
include "syl3anc.mm"
include "r19.42v.mm"
include "sylanbrc.mm"
include "orcd.mm"
include "pm2.61ine.mm"
include "3exp.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "mpd.mm"
include "impbid.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem edglnl
  let vv: setvar v
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  assume edglnl.v: |- V = ( Vtx ` G )
  assume edglnl.e: |- E = ( iEdg ` G )

  disjoint E v
  disjoint G i
  disjoint N i
  disjoint N v
  disjoint i v
  disjoint V i
  disjoint V v
  disjoint E m
  disjoint E n
  disjoint m n
  disjoint m v
  disjoint n v
  disjoint G m
  disjoint G n
  disjoint i m
  disjoint i n
  disjoint N m
  disjoint N n
  disjoint V m
  disjoint V n
  assert |- ( ( G e. UPGraph /\ N e. V ) -> ( U_ v e. ( V \ { N } ) { i e. dom E | ( N e. ( E ` i ) /\ v e. ( E ` i ) ) } u. { i e. dom E | ( E ` i ) = { N } } ) = { i e. dom E | N e. ( E ` i ) } )

  proof
    cG
    cupgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    vv
    cV
    cN
    csn
    #
    cdif
    #
    cN
    vi
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vv
    cv
    #
    @6
    wcel
    #
    wa
    #
    vi
    cE
    cdm
    #
    crab
    ciun
    #
    @6
    @3
    wceq
    #
    vi
    @11
    crab
    #
    cun
    @10
    vv
    @4
    wrex
    #
    vi
    @11
    crab
    #
    @14
    cun
    #
    @7
    vi
    @11
    crab
    #
    @2
    @12
    @16
    @14
    @12
    @16
    wceq
    @2
    @10
    vv
    vi
    @4
    @11
    iunrab
    a1i
    uneq1d
    @2
    @17
    @15
    @13
    wo
    #
    vi
    @11
    crab
    @18
    @15
    @13
    vi
    @11
    unrab
    @2
    @19
    @7
    vi
    @11
    @2
    @5
    @11
    wcel
    #
    wa
    #
    @19
    @7
    @21
    @15
    @7
    @13
    @15
    @7
    wi
    @21
    @10
    @7
    vv
    @4
    @7
    @9
    simpl
    rexlimivw
    a1i
    @21
    @7
    @13
    cN
    @3
    wcel
    #
    @1
    @22
    @0
    @20
    cN
    cV
    snidg
    ad2antlr
    @6
    @3
    cN
    eleq2
    syl5ibrcom
    jaod
    @21
    @6
    cG
    cedg
    cfv
    #
    wcel
    #
    @7
    @19
    wi
    #
    @2
    cE
    wfun
    #
    @20
    @24
    @0
    @26
    @1
    @0
    cG
    cuhgr
    wcel
    @26
    cG
    upgruhgr
    cE
    cG
    edglnl.e
    uhgrfun
    syl
    adantr
    cE
    cG
    @5
    edglnl.e
    iedgedg
    sylan
    @21
    @24
    @6
    vn
    cv
    #
    vm
    cv
    #
    cpr
    #
    wceq
    #
    vm
    cV
    wrex
    vn
    cV
    wrex
    #
    @25
    @0
    @24
    @31
    wi
    @1
    @20
    @0
    @24
    @31
    @6
    @23
    cG
    cV
    vn
    vm
    edglnl.v
    @23
    eqid
    upgredg
    ex
    ad2antrr
    @21
    @30
    @25
    vn
    vm
    cV
    cV
    @21
    @27
    cV
    wcel
    @28
    cV
    wcel
    wa
    #
    wa
    @25
    @30
    cN
    @29
    wcel
    #
    @33
    @8
    @29
    wcel
    #
    wa
    #
    vv
    @4
    wrex
    #
    @29
    @3
    wceq
    #
    wo
    #
    wi
    #
    @21
    @32
    @39
    @1
    @32
    @39
    wi
    @0
    @20
    @1
    @32
    @33
    @38
    @1
    @32
    @33
    w3a
    #
    @38
    wi
    @28
    @27
    @40
    @28
    @27
    wceq
    #
    @38
    @33
    @1
    @41
    @38
    wi
    @32
    @41
    @33
    @38
    @41
    @33
    wa
    @37
    @36
    @41
    @33
    @37
    @41
    @33
    @37
    wi
    cN
    @27
    @27
    cpr
    #
    wcel
    #
    @42
    @3
    wceq
    #
    wi
    @44
    cN
    @27
    csn
    #
    @42
    cN
    @45
    wcel
    #
    @42
    @45
    @3
    @45
    @42
    @27
    dfsn2
    eqcomi
    #
    @46
    cN
    @27
    wceq
    #
    @45
    @3
    wceq
    cN
    @27
    elsni
    @48
    @3
    @45
    cN
    @27
    sneq
    eqcomd
    syl
    syl5eq
    @47
    eleq2s
    @41
    @33
    @43
    @37
    @44
    @41
    @29
    @42
    cN
    @28
    @27
    @27
    preq2
    #
    eleq2d
    @41
    @29
    @42
    @3
    @49
    eqeq1d
    imbi12d
    mpbiri
    imp
    olcd
    expcom
    3ad2ant3
    com12
    @28
    @27
    wne
    #
    @40
    @38
    @50
    @40
    wa
    #
    @36
    @37
    @51
    @33
    @34
    vv
    @4
    wrex
    #
    @36
    @50
    @1
    @32
    @33
    simpr3
    #
    @51
    @33
    @27
    @28
    wne
    @32
    @52
    @53
    @51
    @28
    @27
    @50
    @40
    simpl
    necomd
    @50
    @1
    @32
    @33
    simpr2
    vv
    @27
    @28
    cN
    cV
    prproe
    syl3anc
    @33
    @34
    vv
    @4
    r19.42v
    sylanbrc
    orcd
    ex
    pm2.61ine
    3exp
    ad2antlr
    imp
    @30
    @7
    @33
    @19
    @38
    @6
    @29
    cN
    eleq2
    #
    @30
    @15
    @36
    @13
    @37
    @30
    @10
    @35
    vv
    @4
    @30
    @7
    @33
    @9
    @34
    @54
    @6
    @29
    @8
    eleq2
    anbi12d
    rexbidv
    @6
    @29
    @3
    eqeq1
    orbi12d
    imbi12d
    syl5ibrcom
    rexlimdvva
    syld
    mpd
    impbid
    rabbidva
    syl5eq
    eqtrd
end
