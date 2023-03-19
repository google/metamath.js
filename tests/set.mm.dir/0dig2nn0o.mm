include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "cc0.mm"
include "cdig.mm"
include "cfv.mm"
include "cexp.mm"
include "cfl.mm"
include "cmo.mm"
include "cn.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "2nn.mm"
include "a1i.mm"
include "0nn0.mm"
include "nn0rp0.mm"
include "adantr.mm"
include "nn0digval.mm"
include "syl3anc.mm"
include "cc.mm"
include "2cn.mm"
include "exp0.mm"
include "mp1i.mm"
include "oveq2d.mm"
include "nn0cn.mm"
include "div1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cz.mm"
include "nn0z.mm"
include "flid.mm"
include "syl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "adantl.mm"
include "wne.mm"
include "wb.mm"
include "2z.mm"
include "2ne0.mm"
include "peano2nn0.mm"
include "nn0zd.mm"
include "dvdsval2.mm"
include "mpbird.mm"
include "oddp1even.mm"
include "mod2eq1n2dvds.mm"

theorem 0dig2nn0o
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( 0 ( digit ` 2 ) N ) = 1 )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    wa
    #
    cc0
    cN
    c2
    cdig
    cfv
    co
    #
    cN
    c2
    cc0
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    c1
    @4
    c2
    cn
    wcel
    #
    cc0
    cn0
    wcel
    #
    cN
    cc0
    cpnf
    cico
    co
    wcel
    #
    @5
    @9
    wceq
    @10
    @4
    2nn
    a1i
    @11
    @4
    0nn0
    a1i
    @0
    @12
    @3
    cN
    nn0rp0
    adantr
    c2
    cN
    cc0
    nn0digval
    syl3anc
    @4
    @9
    cN
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    c1
    @4
    @8
    @13
    c2
    cmo
    @4
    @7
    cN
    cfl
    @4
    @7
    cN
    c1
    cdiv
    co
    #
    cN
    @4
    @6
    c1
    cN
    cdiv
    c2
    cc
    wcel
    @6
    c1
    wceq
    @4
    2cn
    c2
    exp0
    mp1i
    oveq2d
    @0
    @15
    cN
    wceq
    @3
    @0
    cN
    cN
    nn0cn
    div1d
    adantr
    eqtrd
    fveq2d
    oveq1d
    @4
    @14
    cN
    c2
    cmo
    co
    #
    c1
    @0
    @14
    @16
    wceq
    @3
    @0
    @13
    cN
    c2
    cmo
    @0
    cN
    cz
    wcel
    #
    @13
    cN
    wceq
    cN
    nn0z
    #
    cN
    flid
    syl
    oveq1d
    adantr
    @4
    @16
    c1
    wceq
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    @4
    @20
    c2
    @1
    cdvds
    wbr
    #
    @4
    @21
    @2
    cz
    wcel
    #
    @3
    @22
    @0
    @2
    nn0z
    adantl
    @4
    c2
    cz
    wcel
    #
    c2
    cc0
    wne
    #
    @1
    cz
    wcel
    #
    @21
    @22
    wb
    @23
    @4
    2z
    a1i
    @24
    @4
    2ne0
    a1i
    @0
    @25
    @3
    @0
    @1
    cN
    peano2nn0
    nn0zd
    adantr
    c2
    @1
    dvdsval2
    syl3anc
    mpbird
    @0
    @20
    @21
    wb
    #
    @3
    @0
    @17
    @26
    @18
    cN
    oddp1even
    syl
    adantr
    mpbird
    @4
    @17
    @19
    @20
    wb
    @0
    @17
    @3
    @18
    adantr
    cN
    mod2eq1n2dvds
    syl
    mpbird
    eqtrd
    eqtrd
    eqtrd
end
