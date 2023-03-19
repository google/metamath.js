include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
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
include "c1.mm"
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
include "adantl.mm"
include "cr.mm"
include "crp.mm"
include "wb.mm"
include "nn0re.mm"
include "2rp.mm"
include "mod0.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem 0dig2nn0e
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ ( N / 2 ) e. NN0 ) -> ( 0 ( digit ` 2 ) N ) = 0 )

  proof
    cN
    cn0
    wcel
    #
    cN
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
    cc0
    @3
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
    @4
    @8
    wceq
    @9
    @3
    2nn
    a1i
    @10
    @3
    0nn0
    a1i
    @0
    @11
    @2
    cN
    nn0rp0
    adantr
    c2
    cN
    cc0
    nn0digval
    syl3anc
    @3
    @8
    cN
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    cc0
    @3
    @7
    @12
    c2
    cmo
    @3
    @6
    cN
    cfl
    @3
    @6
    cN
    c1
    cdiv
    co
    #
    cN
    @3
    @5
    c1
    cN
    cdiv
    c2
    cc
    wcel
    @5
    c1
    wceq
    @3
    2cn
    c2
    exp0
    mp1i
    oveq2d
    @0
    @14
    cN
    wceq
    @2
    @0
    cN
    cN
    nn0cn
    div1d
    adantr
    eqtrd
    fveq2d
    oveq1d
    @3
    @13
    cN
    c2
    cmo
    co
    #
    cc0
    @3
    @12
    cN
    c2
    cmo
    @0
    @12
    cN
    wceq
    #
    @2
    @0
    cN
    cz
    wcel
    @16
    cN
    nn0z
    cN
    flid
    syl
    adantr
    oveq1d
    @3
    @15
    cc0
    wceq
    #
    @1
    cz
    wcel
    #
    @2
    @18
    @0
    @1
    nn0z
    adantl
    @3
    cN
    cr
    wcel
    #
    c2
    crp
    wcel
    @17
    @18
    wb
    @0
    @19
    @2
    cN
    nn0re
    adantr
    2rp
    cN
    c2
    mod0
    sylancl
    mpbird
    eqtrd
    eqtrd
    eqtrd
end
