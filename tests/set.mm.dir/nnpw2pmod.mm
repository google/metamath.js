include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmo.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "crp.mm"
include "nnre.mm"
include "2nn.mm"
include "a1i.mm"
include "cn0.mm"
include "blennnelnn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnexpcld.mm"
include "nnrpd.mm"
include "modeqmodmin.mm"
include "syl2anc.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "nnred.mm"
include "resubcld.mm"
include "nnpw2blen.mm"
include "subge0d.mm"
include "ltsubadd2d.mm"
include "cmul.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "eqcomd.mm"
include "mp1i.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "2timesd.mm"
include "1nn0.mm"
include "expaddd.mm"
include "1cnd.mm"
include "pncan3d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "breq2d.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "mpbird.mm"
include "modid.mm"
include "syl21anc.mm"
include "eqtr2d.mm"
include "nncn.mm"
include "nnz.mm"
include "zmodcld.mm"
include "nn0cnd.mm"
include "subaddd.mm"
include "mpbid.mm"

theorem nnpw2pmod
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> N = ( ( 2 ^ ( ( #b ` N ) - 1 ) ) + ( N mod ( 2 ^ ( ( #b ` N ) - 1 ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
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
    cN
    @3
    cmo
    co
    #
    caddc
    co
    #
    cN
    @0
    cN
    @3
    cmin
    co
    #
    @4
    wceq
    @5
    cN
    wceq
    @0
    @4
    @6
    @3
    cmo
    co
    #
    @6
    @0
    cN
    cr
    wcel
    @3
    crp
    wcel
    #
    @4
    @7
    wceq
    cN
    nnre
    #
    @0
    @3
    @0
    c2
    @2
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @0
    @1
    cn
    wcel
    @2
    cn0
    wcel
    cN
    blennnelnn
    #
    @1
    nnm1nn0
    syl
    #
    nnexpcld
    #
    nnrpd
    #
    cN
    @3
    modeqmodmin
    syl2anc
    @0
    @6
    cr
    wcel
    @8
    cc0
    @6
    cle
    wbr
    #
    @6
    @3
    clt
    wbr
    #
    wa
    #
    @7
    @6
    wceq
    @0
    cN
    @3
    @9
    @0
    @3
    @12
    nnred
    #
    resubcld
    @13
    @0
    @16
    @3
    cN
    cle
    wbr
    #
    cN
    c2
    @1
    cexp
    co
    #
    clt
    wbr
    #
    wa
    cN
    nnpw2blen
    @0
    @14
    @18
    @15
    @20
    @0
    cN
    @3
    @9
    @17
    subge0d
    @0
    @15
    cN
    @3
    @3
    caddc
    co
    #
    clt
    wbr
    @20
    @0
    cN
    @3
    @3
    @9
    @17
    @17
    ltsubadd2d
    @0
    @21
    @19
    cN
    clt
    @0
    c2
    @3
    cmul
    co
    c2
    c1
    cexp
    co
    #
    @3
    cmul
    co
    #
    @21
    @19
    @0
    c2
    @22
    @3
    cmul
    c2
    cc
    wcel
    #
    c2
    @22
    wceq
    @0
    2cn
    @24
    @22
    c2
    c2
    exp1
    eqcomd
    mp1i
    oveq1d
    @0
    @3
    @0
    @3
    @12
    nncnd
    #
    2timesd
    @0
    c2
    c1
    @2
    caddc
    co
    #
    cexp
    co
    @23
    @19
    @0
    c2
    c1
    @2
    @24
    @0
    2cn
    a1i
    @11
    c1
    cn0
    wcel
    @0
    1nn0
    a1i
    expaddd
    @0
    @26
    @1
    c2
    cexp
    @0
    c1
    @1
    @0
    1cnd
    @0
    @1
    @10
    nncnd
    pncan3d
    oveq2d
    eqtr3d
    3eqtr3d
    breq2d
    bitrd
    anbi12d
    mpbird
    @6
    @3
    modid
    syl21anc
    eqtr2d
    @0
    cN
    @3
    @4
    cN
    nncn
    @25
    @0
    @4
    @0
    cN
    @3
    cN
    nnz
    @12
    zmodcld
    nn0cnd
    subaddd
    mpbid
    eqcomd
end
