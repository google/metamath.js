include "c1.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "crelexp.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "wi.mm"
include "simpl.mm"
include "oveq2d.mm"
include "relexp1g.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "eqimss.mm"
include "syl.mm"
include "ex.mm"
include "wn.mm"
include "w3a.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wrel.mm"
include "simp2.mm"
include "simp3.mm"
include "simp1.mm"
include "pm2.21d.mm"
include "3jca.mm"
include "relexprelg.mm"
include "relfld.mm"
include "3syl.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "elnn0.mm"
include "relexpnndm.mm"
include "relexpnnrn.mm"
include "unss12.mm"
include "syl2anc.mm"
include "cid.mm"
include "cres.mm"
include "relexp0g.mm"
include "adantl.mm"
include "dmeqd.mm"
include "dmresi.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rnresi.mm"
include "unssd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "sylc.mm"
include "eqsstrd.mm"
include "dmrnssfld.mm"
include "syl6ss.mm"
include "3expib.mm"
include "pm2.61i.mm"

theorem relexpfld
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN0 /\ R e. V ) -> U. U. ( R ^r N ) C_ U. U. R )

  proof
    cN
    c1
    wceq
    #
    cN
    cn0
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cR
    cN
    crelexp
    co
    #
    cuni
    #
    cuni
    #
    cR
    cuni
    #
    cuni
    #
    wss
    #
    wi
    @0
    @3
    @9
    @0
    @3
    wa
    #
    @6
    @8
    wceq
    @9
    @10
    @5
    @7
    @10
    @4
    cR
    @10
    @4
    cR
    c1
    crelexp
    co
    #
    cR
    @10
    cN
    c1
    cR
    crelexp
    @0
    @3
    simpl
    oveq2d
    @2
    @11
    cR
    wceq
    @0
    @1
    cR
    cV
    relexp1g
    ad2antll
    eqtrd
    unieqd
    unieqd
    @6
    @8
    eqimss
    syl
    ex
    @0
    wn
    #
    @1
    @2
    @9
    @12
    @1
    @2
    w3a
    #
    @6
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    @8
    @13
    @6
    @4
    cdm
    #
    @4
    crn
    #
    cun
    #
    @16
    @13
    @1
    @2
    @0
    cR
    wrel
    #
    wi
    #
    w3a
    @4
    wrel
    @6
    @19
    wceq
    @13
    @1
    @2
    @21
    @12
    @1
    @2
    simp2
    #
    @12
    @1
    @2
    simp3
    #
    @13
    @0
    @20
    @12
    @1
    @2
    simp1
    pm2.21d
    3jca
    cR
    cN
    cV
    relexprelg
    @4
    relfld
    3syl
    @13
    @1
    @2
    @19
    @16
    wss
    #
    @22
    @23
    @1
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @2
    @24
    wi
    #
    cN
    elnn0
    @25
    @27
    @26
    @25
    @2
    @24
    @25
    @2
    wa
    @17
    @14
    wss
    @18
    @15
    wss
    @24
    cR
    cN
    cV
    relexpnndm
    cR
    cN
    cV
    relexpnnrn
    @17
    @14
    @18
    @15
    unss12
    syl2anc
    ex
    @26
    @2
    @24
    @26
    @2
    wa
    #
    @17
    @18
    @16
    @28
    @17
    @16
    wceq
    @17
    @16
    wss
    @28
    @17
    cid
    @16
    cres
    #
    cdm
    @16
    @28
    @4
    @29
    @28
    @4
    cR
    cc0
    crelexp
    co
    #
    @29
    @28
    cN
    cc0
    cR
    crelexp
    @26
    @2
    simpl
    oveq2d
    @2
    @30
    @29
    wceq
    @26
    cR
    cV
    relexp0g
    adantl
    eqtrd
    #
    dmeqd
    @16
    dmresi
    syl6eq
    @17
    @16
    eqimss
    syl
    @28
    @18
    @16
    wceq
    @18
    @16
    wss
    @28
    @18
    @29
    crn
    @16
    @28
    @4
    @29
    @31
    rneqd
    @16
    rnresi
    syl6eq
    @18
    @16
    eqimss
    syl
    unssd
    ex
    jaoi
    sylbi
    sylc
    eqsstrd
    cR
    dmrnssfld
    syl6ss
    3expib
    pm2.61i
end
