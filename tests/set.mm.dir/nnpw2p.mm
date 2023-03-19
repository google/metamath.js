include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "wrex.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "cn0.mm"
include "blennnelnn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "wb.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "adantl.mm"
include "cmo.mm"
include "cz.mm"
include "nnz.mm"
include "2nn.mm"
include "a1i.mm"
include "nnexpcld.mm"
include "zmodfzo.mm"
include "syl2anc.mm"
include "nnpw2pmod.mm"
include "rspcedvd.mm"

theorem nnpw2p
  let vi: setvar i
  let cN: class N
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x

  disjoint N i
  disjoint N r
  disjoint i r
  disjoint k x
  assert |- ( N e. NN -> E. i e. NN0 E. r e. ( 0 ..^ ( 2 ^ i ) ) N = ( ( 2 ^ i ) + r ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    vi
    cv
    #
    cexp
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cc0
    @2
    cfzo
    co
    #
    wrex
    #
    cN
    c2
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    @3
    caddc
    co
    #
    wceq
    #
    vr
    cc0
    @10
    cfzo
    co
    #
    wrex
    #
    vi
    @9
    cn0
    @0
    @8
    cn
    wcel
    @9
    cn0
    wcel
    cN
    blennnelnn
    @8
    nnm1nn0
    syl
    #
    @1
    @9
    wceq
    #
    @7
    @14
    wb
    @0
    @16
    @5
    @12
    vr
    @6
    @13
    @16
    @2
    @10
    cc0
    cfzo
    @1
    @9
    c2
    cexp
    oveq2
    #
    oveq2d
    @16
    @4
    @11
    cN
    @16
    @2
    @10
    @3
    caddc
    @17
    oveq1d
    eqeq2d
    rexeqbidv
    adantl
    @0
    @12
    cN
    @10
    cN
    @10
    cmo
    co
    #
    caddc
    co
    #
    wceq
    #
    vr
    @18
    @13
    @0
    cN
    cz
    wcel
    @10
    cn
    wcel
    @18
    @13
    wcel
    cN
    nnz
    @0
    c2
    @9
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @15
    nnexpcld
    cN
    @10
    zmodfzo
    syl2anc
    @3
    @18
    wceq
    #
    @12
    @20
    wb
    @0
    @21
    @11
    @19
    cN
    @3
    @18
    @10
    caddc
    oveq2
    eqeq2d
    adantl
    cN
    nnpw2pmod
    rspcedvd
    rspcedvd
end
