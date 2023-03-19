include "cn.mm"
include "wcel.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c5.mm"
include "wceq.mm"
include "c2.mm"
include "c1.mm"
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
include "2lgslem3c.mm"
include "syl2an2r.mm"
include "oveq1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cz.mm"
include "nn0z.mm"
include "eqidd.mm"
include "2tp1odd.mm"
include "syl2anc.mm"
include "wb.mm"
include "2z.mm"
include "zmulcld.mm"
include "peano2zd.mm"
include "mod2eq1n2dvds.mm"
include "syl.mm"
include "mpbird.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syld.mm"
include "imp.mm"

theorem 2lgslem3c1
  let cP: class P
  let cN: class N
  let vk: setvar k
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( P e. NN /\ ( P mod 8 ) = 5 ) -> ( N mod 2 ) = 1 )

  proof
    cP
    cn
    wcel
    #
    cP
    c8
    cmo
    co
    c5
    wceq
    #
    cN
    c2
    cmo
    co
    #
    c1
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
    c5
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
    c5
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
    c1
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
    c5
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
    c5
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
    2lgslem3c
    syl2an2r
    @14
    @10
    @2
    @13
    c2
    cmo
    co
    #
    c1
    cN
    @13
    c2
    cmo
    oveq1
    @10
    @19
    c1
    wceq
    #
    c2
    @13
    cdvds
    wbr
    wn
    #
    @10
    @4
    cz
    wcel
    @13
    @13
    wceq
    @21
    @4
    nn0z
    #
    @10
    @13
    eqidd
    @4
    @13
    2tp1odd
    syl2anc
    @10
    @13
    cz
    wcel
    @20
    @21
    wb
    @10
    @12
    @10
    c2
    @4
    c2
    cz
    wcel
    @10
    2z
    a1i
    @22
    zmulcld
    peano2zd
    @13
    mod2eq1n2dvds
    syl
    mpbird
    sylan9eqr
    syl2an2r
    ex
    rexlimdva
    syld
    imp
end
