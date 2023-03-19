include "cn.mm"
include "wcel.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
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
include "2lgslem3a.mm"
include "syl2an2r.mm"
include "oveq1.mm"
include "2cnd.mm"
include "cz.mm"
include "nn0z.mm"
include "2rp.mm"
include "mulmod0.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syld.mm"
include "imp.mm"

theorem 2lgslem3a1
  let cP: class P
  let cN: class N
  let vk: setvar k
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( P e. NN /\ ( P mod 8 ) = 1 ) -> ( N mod 2 ) = 0 )

  proof
    cP
    cn
    wcel
    #
    cP
    c8
    cmo
    co
    c1
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
    c1
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
    c1
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
    c1
    caddc
    co
    #
    wceq
    #
    @13
    @14
    @11
    @7
    @17
    @11
    @6
    @16
    cP
    @11
    @5
    @15
    c1
    caddc
    @10
    @5
    @15
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
    2lgslem3a
    syl2an2r
    @13
    @10
    @2
    @12
    c2
    cmo
    co
    #
    cc0
    cN
    @12
    c2
    cmo
    oveq1
    @10
    @19
    @4
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
    @12
    @20
    c2
    cmo
    @10
    c2
    @4
    @10
    2cnd
    @18
    mulcomd
    oveq1d
    @10
    @4
    cz
    wcel
    c2
    crp
    wcel
    @21
    cc0
    wceq
    @4
    nn0z
    2rp
    @4
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
