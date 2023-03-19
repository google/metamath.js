include "cn.mm"
include "wcel.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c7.mm"
include "wceq.mm"
include "c2.mm"
include "cc0.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cn0.mm"
include "wrex.mm"
include "crp.mm"
include "wi.mm"
include "nnnn0.mm"
include "8nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "modmuladdnn0.mm"
include "sylancl.mm"
include "wa.mm"
include "simpr.mm"
include "nn0cn.mm"
include "cc.mm"
include "8cn.mm"
include "a1i.mm"
include "mulcomd.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "2lgslem3d.mm"
include "syl2an2r.mm"
include "oveq1.mm"
include "c1.mm"
include "2t1e2.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "1cnd.mm"
include "w3a.mm"
include "adddi.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "addcld.mm"
include "3eqtrd.mm"
include "cz.mm"
include "peano2nn0.mm"
include "nn0zd.mm"
include "2rp.mm"
include "mulmod0.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syld.mm"
include "imp.mm"

theorem 2lgslem3d1
  let cP: class P
  let cN: class N
  let vk: setvar k
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( P e. NN /\ ( P mod 8 ) = 7 ) -> ( N mod 2 ) = 0 )

  proof
    cP
    cn
    wcel
    #
    cP
    c8
    cmo
    co
    c7
    wceq
    #
    cN
    c2
    cmo
    co
    #
    cc0
    wceq
    #
    @0
    @1
    cP
    vk
    cv
    #
    c8
    cmul
    co
    #
    c7
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    @3
    @0
    cP
    cn0
    wcel
    c8
    crp
    wcel
    #
    @1
    @8
    wi
    cP
    nnnn0
    c8
    cn
    wcel
    @9
    8nn
    c8
    nnrp
    ax-mp
    cP
    c7
    vk
    c8
    modmuladdnn0
    sylancl
    @0
    @7
    @3
    vk
    cn0
    @0
    @4
    cn0
    wcel
    #
    wa
    #
    @7
    @3
    @11
    @10
    @7
    cN
    c2
    @4
    cmul
    co
    #
    c2
    caddc
    co
    #
    wceq
    #
    @3
    @0
    @10
    simpr
    #
    @11
    @10
    @7
    cP
    c8
    @4
    cmul
    co
    #
    c7
    caddc
    co
    #
    wceq
    #
    @14
    @15
    @11
    @7
    @18
    @11
    @6
    @17
    cP
    @11
    @5
    @16
    c7
    caddc
    @10
    @5
    @16
    wceq
    @0
    @10
    @4
    c8
    @4
    nn0cn
    #
    c8
    cc
    wcel
    @10
    8cn
    a1i
    mulcomd
    adantl
    oveq1d
    eqeq2d
    biimpa
    cP
    @4
    cN
    2lgslem2.n
    2lgslem3d
    syl2an2r
    @14
    @10
    @2
    @13
    c2
    cmo
    co
    #
    cc0
    cN
    @13
    c2
    cmo
    oveq1
    @10
    @20
    @4
    c1
    caddc
    co
    #
    c2
    cmul
    co
    #
    c2
    cmo
    co
    #
    cc0
    @10
    @13
    @22
    c2
    cmo
    @10
    @13
    @12
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    c2
    @21
    cmul
    co
    #
    @22
    @10
    c2
    @24
    @12
    caddc
    c2
    @24
    wceq
    @10
    @24
    c2
    2t1e2
    eqcomi
    a1i
    oveq2d
    @10
    c2
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @25
    @26
    wceq
    @10
    2cnd
    #
    @19
    @10
    1cnd
    #
    @27
    @28
    @29
    w3a
    @26
    @25
    c2
    @4
    c1
    adddi
    eqcomd
    syl3anc
    @10
    c2
    @21
    @30
    @10
    @4
    c1
    @19
    @31
    addcld
    mulcomd
    3eqtrd
    oveq1d
    @10
    @21
    cz
    wcel
    c2
    crp
    wcel
    @23
    cc0
    wceq
    @10
    @21
    @4
    peano2nn0
    nn0zd
    2rp
    @21
    c2
    mulmod0
    sylancl
    eqtrd
    sylan9eqr
    syl2an2r
    ex
    rexlimdva
    syld
    imp
end
