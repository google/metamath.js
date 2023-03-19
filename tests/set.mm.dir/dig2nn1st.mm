include "cn.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdig.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmo.mm"
include "cn0.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "2nn.mm"
include "a1i.mm"
include "blennnelnn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "nn0digval.mm"
include "syl3anc.mm"
include "cdvds.mm"
include "wn.mm"
include "n2dvds1.mm"
include "clogb.mm"
include "caddc.mm"
include "blennn.mm"
include "oveq1d.mm"
include "cc.mm"
include "cuz.mm"
include "crp.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "nnrp.mm"
include "relogbzcl.mm"
include "sylancr.mm"
include "flcld.mm"
include "zcnd.mm"
include "pncan1.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "fldivexpfllog2.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "wb.mm"
include "2re.mm"
include "reexpcld.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "nn0zd.mm"
include "expne0d.mm"
include "redivcld.mm"
include "mod2eq1n2dvds.mm"
include "mpbird.mm"

theorem dig2nn1st
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( ( ( #b ` N ) - 1 ) ( digit ` 2 ) N ) = 1 )

  proof
    cN
    cn
    wcel
    #
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    #
    cN
    c2
    cdig
    cfv
    co
    #
    cN
    c2
    @2
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
    @0
    c2
    cn
    wcel
    #
    @2
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
    @3
    @7
    wceq
    @8
    @0
    2nn
    a1i
    @0
    @1
    cn
    wcel
    @9
    cN
    blennnelnn
    @1
    nnm1nn0
    syl
    #
    @0
    cN
    cr
    wcel
    cc0
    cN
    cle
    wbr
    @10
    cN
    nnre
    #
    @0
    cN
    cN
    nnnn0
    nn0ge0d
    cN
    elrege0
    sylanbrc
    c2
    cN
    @2
    nn0digval
    syl3anc
    @0
    @7
    c1
    wceq
    #
    c2
    @6
    cdvds
    wbr
    #
    wn
    #
    @0
    @14
    c2
    c1
    cdvds
    wbr
    n2dvds1
    @0
    @6
    c1
    c2
    cdvds
    @0
    @6
    cN
    c2
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    @0
    @5
    @19
    cfl
    @0
    @4
    @18
    cN
    cdiv
    @0
    @2
    @17
    c2
    cexp
    @0
    @2
    @17
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @17
    @0
    @1
    @21
    c1
    cmin
    cN
    blennn
    oveq1d
    @0
    @17
    cc
    wcel
    @22
    @17
    wceq
    @0
    @17
    @0
    @16
    @0
    c2
    c2
    cuz
    cfv
    wcel
    #
    cN
    crp
    wcel
    #
    @16
    cr
    wcel
    c2
    cz
    wcel
    @23
    2z
    c2
    uzid
    ax-mp
    cN
    nnrp
    #
    c2
    cN
    relogbzcl
    sylancr
    flcld
    zcnd
    @17
    pncan1
    syl
    eqtrd
    oveq2d
    oveq2d
    fveq2d
    @0
    @24
    @20
    c1
    wceq
    @25
    cN
    fldivexpfllog2
    syl
    eqtrd
    breq2d
    mtbiri
    @0
    @6
    cz
    wcel
    @13
    @15
    wb
    @0
    @5
    @0
    cN
    @4
    @12
    @0
    c2
    @2
    c2
    cr
    wcel
    @0
    2re
    a1i
    @11
    reexpcld
    @0
    c2
    @2
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    @0
    @2
    @11
    nn0zd
    expne0d
    redivcld
    flcld
    @6
    mod2eq1n2dvds
    syl
    mpbird
    eqtrd
end
