include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ckgen.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "crest.mm"
include "ccmp.mm"
include "cres.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ccom.mm"
include "kgencn.mm"
include "crn.mm"
include "rncmp.mm"
include "adantl.mm"
include "wss.mm"
include "cuni.mm"
include "simprr.mm"
include "eqid.mm"
include "cnf.mm"
include "frn.mm"
include "3syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "ad3antrrr.mm"
include "sseqtr4d.mm"
include "vex.mm"
include "rnex.mm"
include "elpw.mm"
include "sylibr.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "reseq2.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "wb.mm"
include "simplll.mm"
include "ssid.mm"
include "a1i.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cnco.mm"
include "ex.mm"
include "cores.mm"
include "ax-mp.mm"
include "eleq1i.mm"
include "syl6ib.mm"
include "syld.mm"
include "ralrimdvva.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "cid.mm"
include "elpwi.mm"
include "resabs1d.mm"
include "idcn.mm"
include "sseqtrd.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "coeq2.mm"
include "coires1.mm"
include "syl9r.mm"
include "com23.mm"
include "ralrimdva.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem kgencn2
  let vz: setvar z
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x

  disjoint g z
  disjoint F g
  disjoint F z
  disjoint J g
  disjoint J z
  disjoint K g
  disjoint K z
  disjoint X g
  disjoint X z
  disjoint Y g
  disjoint Y z
  disjoint g k
  disjoint g x
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint x z
  disjoint F x
  disjoint J k
  disjoint J x
  disjoint K k
  disjoint K x
  disjoint X k
  disjoint X x
  disjoint Y k
  disjoint Y x
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( ( kGen ` J ) Cn K ) <-> ( F : X --> Y /\ A. z e. Comp A. g e. ( z Cn J ) ( F o. g ) e. ( z Cn K ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    ckgen
    cfv
    cK
    ccn
    co
    wcel
    cX
    cY
    cF
    wf
    #
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    cF
    @4
    cres
    #
    @5
    cK
    ccn
    co
    #
    wcel
    #
    wi
    #
    vk
    cX
    cpw
    #
    wral
    #
    wa
    @3
    cF
    vg
    cv
    #
    ccom
    #
    vz
    cv
    #
    cK
    ccn
    co
    #
    wcel
    #
    vg
    @15
    cJ
    ccn
    co
    #
    wral
    #
    vz
    ccmp
    wral
    #
    wa
    vk
    cF
    cJ
    cK
    cX
    cY
    kgencn
    @2
    @3
    @12
    @20
    @2
    @3
    wa
    #
    @12
    @20
    @21
    @12
    @17
    vz
    vg
    ccmp
    @18
    @21
    @15
    ccmp
    wcel
    #
    @13
    @18
    wcel
    #
    wa
    #
    wa
    #
    @12
    cF
    @13
    crn
    #
    cres
    #
    cJ
    @26
    crest
    co
    #
    cK
    ccn
    co
    #
    wcel
    #
    @17
    @25
    @12
    @28
    ccmp
    wcel
    #
    @30
    @24
    @31
    @21
    @13
    @15
    cJ
    rncmp
    adantl
    @25
    @26
    @11
    wcel
    #
    @12
    @31
    @30
    wi
    #
    wi
    @25
    @26
    cX
    wss
    #
    @32
    @25
    @26
    cJ
    cuni
    #
    cX
    @25
    @23
    @15
    cuni
    #
    @35
    @13
    wf
    @26
    @35
    wss
    @21
    @22
    @23
    simprr
    #
    @13
    @15
    cJ
    @36
    @35
    @36
    eqid
    @35
    eqid
    #
    cnf
    @36
    @35
    @13
    frn
    3syl
    @0
    cX
    @35
    wceq
    #
    @1
    @3
    @24
    cX
    cJ
    toponuni
    #
    ad3antrrr
    sseqtr4d
    #
    @26
    cX
    @13
    vg
    vex
    rnex
    elpw
    sylibr
    @10
    @33
    vk
    @26
    @11
    @4
    @26
    wceq
    #
    @6
    @31
    @9
    @30
    @42
    @5
    @28
    ccmp
    @4
    @26
    cJ
    crest
    oveq2
    #
    eleq1d
    @42
    @7
    @27
    @8
    @29
    @4
    @26
    cF
    reseq2
    @42
    @5
    @28
    cK
    ccn
    @43
    oveq1d
    eleq12d
    imbi12d
    rspcv
    syl
    mpid
    @25
    @30
    @27
    @13
    ccom
    #
    @16
    wcel
    #
    @17
    @25
    @13
    @15
    @28
    ccn
    co
    wcel
    #
    @30
    @45
    wi
    @25
    @23
    @46
    @37
    @25
    @0
    @26
    @26
    wss
    #
    @34
    @23
    @46
    wb
    @0
    @1
    @3
    @24
    simplll
    @47
    @25
    @26
    ssid
    #
    a1i
    @41
    @26
    @13
    @15
    cJ
    cX
    cnrest2
    syl3anc
    mpbid
    @46
    @30
    @45
    @13
    @27
    @15
    @28
    cK
    cnco
    ex
    syl
    @44
    @14
    @16
    @47
    @44
    @14
    wceq
    @48
    cF
    @13
    @26
    cores
    ax-mp
    eleq1i
    syl6ib
    syld
    ralrimdvva
    @21
    @20
    @10
    vk
    @11
    @21
    @4
    @11
    wcel
    #
    wa
    #
    @6
    @20
    @9
    @6
    @20
    @14
    @8
    wcel
    #
    vg
    @5
    cJ
    ccn
    co
    #
    wral
    #
    @50
    @9
    @19
    @53
    vz
    @5
    ccmp
    @15
    @5
    wceq
    #
    @17
    @51
    vg
    @18
    @52
    @15
    @5
    cJ
    ccn
    oveq1
    @54
    @16
    @8
    @14
    @15
    @5
    cK
    ccn
    oveq1
    eleq2d
    raleqbidv
    rspcv
    @50
    @53
    cF
    cid
    @4
    cres
    #
    ccom
    #
    @8
    wcel
    #
    @9
    @50
    @55
    @52
    wcel
    @53
    @57
    wi
    @50
    cid
    cX
    cres
    #
    @4
    cres
    #
    @55
    @52
    @50
    cid
    @4
    cX
    @49
    @4
    cX
    wss
    @21
    @4
    cX
    elpwi
    adantl
    #
    resabs1d
    @50
    @58
    cJ
    cJ
    ccn
    co
    wcel
    #
    @4
    @35
    wss
    @59
    @52
    wcel
    @0
    @61
    @1
    @3
    @49
    cJ
    cX
    idcn
    ad3antrrr
    @50
    @4
    cX
    @35
    @60
    @0
    @39
    @1
    @3
    @49
    @40
    ad3antrrr
    sseqtrd
    @4
    @58
    cJ
    cJ
    @35
    @38
    cnrest
    syl2anc
    eqeltrrd
    @51
    @57
    vg
    @55
    @52
    @13
    @55
    wceq
    @14
    @56
    @8
    @13
    @55
    cF
    coeq2
    eleq1d
    rspcv
    syl
    @56
    @7
    @8
    cF
    @4
    coires1
    eleq1i
    syl6ib
    syl9r
    com23
    ralrimdva
    impbid
    pm5.32da
    bitrd
end
