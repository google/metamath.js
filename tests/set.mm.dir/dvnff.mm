include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "wa.mm"
include "cn0.mm"
include "cdm.mm"
include "cdvn.mm"
include "wf.mm"
include "cvv.mm"
include "cv.mm"
include "cdv.mm"
include "cmpt.mm"
include "c1st.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cc0.mm"
include "cseq.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cfv.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "adantll.mm"
include "dmexg.mm"
include "ad2antlr.mm"
include "cnex.mm"
include "a1i.mm"
include "wss.mm"
include "wb.mm"
include "elpm2g.mm"
include "mpan.mm"
include "biimpa.mm"
include "simpld.mm"
include "adantr.mm"
include "fpmg.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "vex.mm"
include "algrflem.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "dvfg.mm"
include "ad2antrr.mm"
include "recnprss.mm"
include "simprl.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simprd.mm"
include "sstrd.mm"
include "dvbss.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "syl5eqel.mm"
include "seqf.mm"
include "dvnfval.mm"
include "sylan.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem dvnff
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let cN: class N
  let vs: setvar s


  assert |- ( ( S e. { RR , CC } /\ F e. ( CC ^pm S ) ) -> ( S Dn F ) : NN0 --> ( CC ^pm dom F ) )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    #
    wcel
    #
    wa
    #
    cn0
    cc
    cF
    cdm
    #
    cpm
    co
    #
    cS
    cF
    cdvn
    co
    #
    wf
    cn0
    @6
    vx
    cvv
    cS
    vx
    cv
    #
    cdv
    co
    #
    cmpt
    #
    c1st
    ccom
    #
    cn0
    cF
    csn
    cxp
    #
    cc0
    cseq
    #
    wf
    @4
    vk
    vn
    @11
    @6
    @12
    cc0
    cn0
    nn0uz
    @4
    0zd
    @4
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @14
    @12
    cfv
    #
    cF
    @6
    @3
    @15
    @17
    cF
    wceq
    @1
    cn0
    cF
    @14
    @2
    fvconst2g
    adantll
    @16
    @5
    cvv
    wcel
    #
    cc
    cvv
    wcel
    #
    @5
    cc
    cF
    wf
    #
    cF
    @6
    wcel
    @3
    @18
    @1
    @15
    cF
    @2
    dmexg
    #
    ad2antlr
    @19
    @16
    cnex
    a1i
    @4
    @20
    @15
    @4
    @20
    @5
    cS
    wss
    #
    @1
    @3
    @20
    @22
    wa
    #
    @19
    @1
    @3
    @23
    wb
    cnex
    cc
    cS
    cF
    cvv
    @0
    elpm2g
    mpan
    biimpa
    #
    simpld
    adantr
    @5
    cc
    cF
    cvv
    cvv
    fpmg
    syl3anc
    eqeltrd
    @4
    @14
    @6
    wcel
    #
    vn
    cv
    #
    @6
    wcel
    #
    wa
    #
    wa
    #
    @14
    @26
    @11
    co
    #
    cS
    @14
    cdv
    co
    #
    @6
    @30
    @14
    @10
    cfv
    #
    @31
    @14
    @26
    @10
    vk
    vex
    #
    vn
    vex
    algrflem
    @14
    cvv
    wcel
    @32
    @31
    wceq
    @33
    vx
    @14
    @9
    @31
    cvv
    @10
    @8
    @14
    cS
    cdv
    oveq2
    @10
    eqid
    #
    cS
    @14
    cdv
    ovex
    fvmpt
    ax-mp
    eqtri
    @29
    @19
    @18
    @31
    cdm
    #
    cc
    @31
    wf
    #
    @35
    @5
    wss
    @31
    @6
    wcel
    @19
    @29
    cnex
    a1i
    @3
    @18
    @1
    @28
    @21
    ad2antlr
    #
    @1
    @36
    @3
    @28
    cS
    @14
    dvfg
    ad2antrr
    @29
    @35
    @14
    cdm
    #
    @5
    @29
    @38
    cS
    @14
    @1
    cS
    cc
    wss
    #
    @3
    @28
    cS
    recnprss
    #
    ad2antrr
    @29
    @38
    cc
    @14
    wf
    #
    @38
    @5
    wss
    #
    @29
    @25
    @41
    @42
    wa
    #
    @4
    @25
    @27
    simprl
    @29
    @19
    @18
    @25
    @43
    wb
    cnex
    @37
    cc
    @5
    @14
    cvv
    cvv
    elpm2g
    sylancr
    mpbid
    #
    simpld
    @29
    @38
    @5
    cS
    @29
    @41
    @42
    @44
    simprd
    #
    @4
    @22
    @28
    @4
    @20
    @22
    @24
    simprd
    adantr
    sstrd
    dvbss
    @45
    sstrd
    cc
    @5
    @35
    @31
    cvv
    cvv
    elpm2r
    syl22anc
    syl5eqel
    seqf
    @4
    cn0
    @6
    @7
    @13
    @1
    @39
    @3
    @7
    @13
    wceq
    @40
    vx
    cS
    cF
    @10
    @34
    dvnfval
    sylan
    feq1d
    mpbird
end
