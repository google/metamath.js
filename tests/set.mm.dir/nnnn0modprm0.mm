include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cmo.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cn.mm"
include "prmnn.mm"
include "adantr.mm"
include "fzo0sn0fzo1.mm"
include "syl.mm"
include "eleq2d.mm"
include "wo.mm"
include "wi.mm"
include "elun.mm"
include "elsni.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "cz.mm"
include "cc.mm"
include "elfzoelz.mm"
include "zcn.mm"
include "mul02.mm"
include "oveq2d.mm"
include "00id.mm"
include "syl6eq.mm"
include "3syl.mm"
include "adantl.mm"
include "oveq1d.mm"
include "crp.mm"
include "nnrp.mm"
include "0mod.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "ex.mm"
include "simpl.mm"
include "simprr.mm"
include "modprm0.mm"
include "syl3anc.mm"
include "jaoi.mm"
include "sylbi.mm"
include "com12.mm"
include "sylbid.mm"
include "3impia.mm"

theorem nnnn0modprm0
  let cP: class P
  let vj: setvar j
  let cI: class I
  let cN: class N

  disjoint I j
  disjoint N j
  disjoint P j
  assert |- ( ( P e. Prime /\ N e. ( 1 ..^ P ) /\ I e. ( 0 ..^ P ) ) -> E. j e. ( 0 ..^ P ) ( ( I + ( j x. N ) ) mod P ) = 0 )

  proof
    cP
    cprime
    wcel
    #
    cN
    c1
    cP
    cfzo
    co
    #
    wcel
    #
    cI
    cc0
    cP
    cfzo
    co
    #
    wcel
    #
    cI
    vj
    cv
    #
    cN
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    cc0
    wceq
    #
    vj
    @3
    wrex
    #
    @0
    @2
    wa
    #
    @4
    cI
    cc0
    csn
    #
    @1
    cun
    #
    wcel
    #
    @10
    @11
    @3
    @13
    cI
    @11
    cP
    cn
    wcel
    #
    @3
    @13
    wceq
    @0
    @15
    @2
    cP
    prmnn
    #
    adantr
    cP
    fzo0sn0fzo1
    syl
    eleq2d
    @14
    @11
    @10
    @14
    cI
    @12
    wcel
    #
    cI
    @1
    wcel
    #
    wo
    @11
    @10
    wi
    #
    cI
    @12
    @1
    elun
    @17
    @19
    @18
    @17
    cI
    cc0
    wceq
    #
    @19
    cI
    cc0
    elsni
    @20
    @11
    @10
    @20
    @11
    wa
    #
    @10
    cc0
    @6
    caddc
    co
    #
    cP
    cmo
    co
    #
    cc0
    wceq
    #
    vj
    @3
    wrex
    #
    @11
    @25
    @20
    @11
    cc0
    @3
    wcel
    #
    cc0
    cc0
    cN
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    cc0
    wceq
    #
    @25
    @0
    @26
    @2
    @0
    @15
    @26
    @16
    cP
    lbfzo0
    sylibr
    adantr
    @11
    @29
    cc0
    cP
    cmo
    co
    #
    cc0
    @11
    @28
    cc0
    cP
    cmo
    @2
    @28
    cc0
    wceq
    #
    @0
    @2
    cN
    cz
    wcel
    cN
    cc
    wcel
    #
    @32
    cN
    c1
    cP
    elfzoelz
    cN
    zcn
    @33
    @28
    cc0
    cc0
    caddc
    co
    cc0
    @33
    @27
    cc0
    cc0
    caddc
    cN
    mul02
    oveq2d
    00id
    syl6eq
    3syl
    adantl
    oveq1d
    @0
    @31
    cc0
    wceq
    #
    @2
    @0
    @15
    cP
    crp
    wcel
    @34
    @16
    cP
    nnrp
    cP
    0mod
    3syl
    adantr
    eqtrd
    @24
    @30
    vj
    cc0
    @3
    @5
    cc0
    wceq
    #
    @23
    @29
    cc0
    @35
    @22
    @28
    cP
    cmo
    @35
    @6
    @27
    cc0
    caddc
    @5
    cc0
    cN
    cmul
    oveq1
    oveq2d
    oveq1d
    eqeq1d
    rspcev
    syl2anc
    adantl
    @21
    @9
    @24
    vj
    @3
    @20
    @9
    @24
    wb
    @11
    @20
    @8
    @23
    cc0
    @20
    @7
    @22
    cP
    cmo
    cI
    cc0
    @6
    caddc
    oveq1
    oveq1d
    eqeq1d
    adantr
    rexbidv
    mpbird
    ex
    syl
    @18
    @11
    @10
    @18
    @11
    wa
    @0
    @2
    @18
    @10
    @11
    @0
    @18
    @0
    @2
    simpl
    adantl
    @18
    @0
    @2
    simprr
    @18
    @11
    simpl
    cP
    vj
    cI
    cN
    modprm0
    syl3anc
    ex
    jaoi
    sylbi
    com12
    sylbid
    3impia
end
