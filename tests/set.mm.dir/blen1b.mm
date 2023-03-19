include "cn0.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "wo.mm"
include "cn.mm"
include "wi.mm"
include "elnn0.mm"
include "c2.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "caddc.mm"
include "blennn.mm"
include "eqeq1d.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cmin.mm"
include "crp.mm"
include "wne.mm"
include "cr.mm"
include "2rp.mm"
include "a1i.mm"
include "nnrp.mm"
include "1ne2.mm"
include "necomi.mm"
include "relogbcl.mm"
include "syl3anc.mm"
include "flcld.mm"
include "zcnd.mm"
include "1cnd.mm"
include "addlsub.mm"
include "1m1e0.mm"
include "eqeq2d.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "flbi.mm"
include "sylancl.mm"
include "3bitrd.mm"
include "0p1e1.mm"
include "breq2i.mm"
include "anbi2i.mm"
include "nnlog2ge0lt1.mm"
include "biimpar.mm"
include "olcd.mm"
include "ex.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "orc.mm"
include "a1d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "fveq2.mm"
include "blen0.mm"
include "syl6eq.mm"
include "blen1.mm"
include "impbid1.mm"

theorem blen1b
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( ( #b ` N ) = 1 <-> ( N = 0 \/ N = 1 ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cblen
    cfv
    #
    c1
    wceq
    #
    cN
    cc0
    wceq
    #
    cN
    c1
    wceq
    #
    wo
    #
    @0
    cN
    cn
    wcel
    #
    @3
    wo
    @2
    @5
    wi
    #
    cN
    elnn0
    @6
    @7
    @3
    @6
    @2
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    c1
    wceq
    #
    @5
    @6
    @1
    @10
    c1
    cN
    blennn
    eqeq1d
    @6
    @11
    cc0
    @8
    cle
    wbr
    #
    @8
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @5
    @6
    @11
    @9
    c1
    c1
    cmin
    co
    #
    wceq
    @9
    cc0
    wceq
    #
    @15
    @6
    @9
    c1
    c1
    @6
    @9
    @6
    @8
    @6
    c2
    crp
    wcel
    #
    cN
    crp
    wcel
    c2
    c1
    wne
    #
    @8
    cr
    wcel
    #
    @18
    @6
    2rp
    a1i
    cN
    nnrp
    @19
    @6
    c1
    c2
    1ne2
    necomi
    a1i
    c2
    cN
    relogbcl
    syl3anc
    #
    flcld
    zcnd
    @6
    1cnd
    #
    @22
    addlsub
    @6
    @16
    cc0
    @9
    @16
    cc0
    wceq
    @6
    1m1e0
    a1i
    eqeq2d
    @6
    @20
    cc0
    cz
    wcel
    @17
    @15
    wb
    @21
    0z
    @8
    cc0
    flbi
    sylancl
    3bitrd
    @15
    @12
    @8
    c1
    clt
    wbr
    #
    wa
    #
    @6
    @5
    @14
    @23
    @12
    @13
    c1
    @8
    clt
    0p1e1
    breq2i
    anbi2i
    @6
    @24
    @5
    @6
    @24
    wa
    @4
    @3
    @6
    @4
    @24
    cN
    nnlog2ge0lt1
    biimpar
    olcd
    ex
    syl5bi
    sylbid
    sylbid
    @3
    @5
    @2
    @3
    @4
    orc
    a1d
    jaoi
    sylbi
    @3
    @2
    @4
    @3
    @1
    cc0
    cblen
    cfv
    c1
    cN
    cc0
    cblen
    fveq2
    blen0
    syl6eq
    @4
    @1
    c1
    cblen
    cfv
    c1
    cN
    c1
    cblen
    fveq2
    blen1
    syl6eq
    jaoi
    impbid1
end
