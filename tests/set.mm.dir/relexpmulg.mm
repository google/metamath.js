include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "crelexp.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "relexpmulnn.mm"
include "3adantl3.mm"
include "expcom.mm"
include "wn.mm"
include "simprr.mm"
include "simpll.mm"
include "oveq2d.mm"
include "simplr.mm"
include "nncnd.mm"
include "mul01d.mm"
include "3eqtrd.mm"
include "simpl.mm"
include "nnnle0.mm"
include "adantl.mm"
include "breq2d.mm"
include "mtbird.mm"
include "syl.mm"
include "mth8.mm"
include "sylc.mm"
include "pm2.21d.mm"
include "exp32.mm"
include "3impd.mm"
include "ex.mm"
include "jaoi.mm"
include "sylbi.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "simpr1.mm"
include "relexp0g.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cvv.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "relexpiidm.mm"
include "simpr2.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "eqtr2d.mm"
include "jaod.mm"
include "syl5bi.mm"
include "impcom.mm"

theorem relexpmulg
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V


  assert |- ( ( ( R e. V /\ I = ( J x. K ) /\ ( I = 0 -> J <_ K ) ) /\ ( J e. NN0 /\ K e. NN0 ) ) -> ( ( R ^r J ) ^r K ) = ( R ^r I ) )

  proof
    cJ
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    cR
    cV
    wcel
    #
    cI
    cJ
    cK
    cmul
    co
    #
    wceq
    #
    cI
    cc0
    wceq
    #
    cJ
    cK
    cle
    wbr
    #
    wi
    #
    w3a
    #
    cR
    cJ
    crelexp
    co
    #
    cK
    crelexp
    co
    #
    cR
    cI
    crelexp
    co
    #
    wceq
    #
    @1
    @0
    @8
    @12
    wi
    #
    @0
    cJ
    cn
    wcel
    #
    cJ
    cc0
    wceq
    #
    wo
    @1
    @13
    cJ
    elnn0
    @1
    @14
    @13
    @15
    @1
    cK
    cn
    wcel
    #
    cK
    cc0
    wceq
    #
    wo
    @14
    @13
    wi
    #
    cK
    elnn0
    @16
    @18
    @17
    @14
    @16
    @13
    @8
    @14
    @16
    wa
    #
    @12
    @2
    @4
    @19
    @12
    @7
    cR
    cI
    cJ
    cK
    cV
    relexpmulnn
    3adantl3
    expcom
    expcom
    @17
    @14
    @13
    @17
    @14
    wa
    #
    @2
    @4
    @7
    @12
    @20
    @2
    @4
    @7
    @12
    wi
    @20
    @2
    @4
    wa
    #
    wa
    #
    @7
    @12
    @22
    @5
    @6
    wn
    #
    @7
    wn
    @22
    cI
    @3
    cJ
    cc0
    cmul
    co
    cc0
    @20
    @2
    @4
    simprr
    @22
    cK
    cc0
    cJ
    cmul
    @17
    @14
    @21
    simpll
    oveq2d
    @22
    cJ
    @22
    cJ
    @17
    @14
    @21
    simplr
    nncnd
    mul01d
    3eqtrd
    @22
    @20
    @23
    @20
    @21
    simpl
    @20
    @6
    cJ
    cc0
    cle
    wbr
    #
    @14
    @24
    wn
    @17
    cJ
    nnnle0
    adantl
    @20
    cK
    cc0
    cJ
    cle
    @17
    @14
    simpl
    breq2d
    mtbird
    syl
    @5
    @6
    mth8
    sylc
    pm2.21d
    exp32
    3impd
    ex
    jaoi
    sylbi
    @1
    @15
    @13
    @1
    @15
    wa
    #
    @8
    @12
    @25
    @8
    wa
    #
    @10
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    cK
    crelexp
    co
    #
    @30
    @11
    @26
    @9
    @30
    cK
    crelexp
    @26
    @9
    cR
    cc0
    crelexp
    co
    #
    @30
    @26
    cJ
    cc0
    cR
    crelexp
    @1
    @15
    @8
    simplr
    #
    oveq2d
    @26
    @2
    @32
    @30
    wceq
    @25
    @2
    @4
    @7
    simpr1
    #
    cR
    cV
    relexp0g
    syl
    #
    eqtrd
    oveq1d
    @26
    @29
    cvv
    wcel
    #
    @1
    @31
    @30
    wceq
    @26
    @2
    @36
    @34
    @2
    @27
    cvv
    wcel
    @28
    cvv
    wcel
    @36
    cR
    cV
    dmexg
    cR
    cV
    rnexg
    @27
    @28
    cvv
    cvv
    unexg
    syl2anc
    syl
    @1
    @15
    @8
    simpll
    #
    @29
    cK
    cvv
    relexpiidm
    syl2anc
    @26
    @11
    @32
    @30
    @26
    cI
    cc0
    cR
    crelexp
    @26
    cI
    @3
    cc0
    cK
    cmul
    co
    cc0
    @25
    @2
    @4
    @7
    simpr2
    @26
    cJ
    cc0
    cK
    cmul
    @33
    oveq1d
    @26
    cK
    @26
    cK
    @37
    nn0cnd
    mul02d
    3eqtrd
    oveq2d
    @35
    eqtr2d
    3eqtrd
    ex
    ex
    jaod
    syl5bi
    impcom
    impcom
end
