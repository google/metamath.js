include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "c2.mm"
include "clogb.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "0le0.mm"
include "cc.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "1ne2.mm"
include "necomi.mm"
include "logb1.mm"
include "mp3an.mm"
include "breqtrri.mm"
include "0lt1.mm"
include "eqbrtri.mm"
include "pm3.2i.mm"
include "oveq2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "mpbiri.mm"
include "cuz.mm"
include "cfv.mm"
include "crp.mm"
include "wb.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "a1i.mm"
include "nnrp.mm"
include "logbge0b.mm"
include "syl2anc.mm"
include "logblt1b.mm"
include "cfl.mm"
include "caddc.mm"
include "df-2.mm"
include "breq2i.mm"
include "anbi2d.mm"
include "cr.mm"
include "nnre.mm"
include "1zzd.mm"
include "flbi.mm"
include "bitr4d.mm"
include "nnz.mm"
include "flid.mm"
include "syl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "simpr.mm"
include "eqtrd.mm"
include "ex.mm"
include "sylbid.mm"
include "impbid2.mm"

theorem nnlog2ge0lt1
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( N = 1 <-> ( 0 <_ ( 2 logb N ) /\ ( 2 logb N ) < 1 ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    wceq
    #
    cc0
    c2
    cN
    clogb
    co
    #
    cle
    wbr
    #
    @2
    c1
    clt
    wbr
    #
    wa
    #
    @1
    @5
    cc0
    c2
    c1
    clogb
    co
    #
    cle
    wbr
    #
    @6
    c1
    clt
    wbr
    #
    wa
    @7
    @8
    cc0
    cc0
    @6
    cle
    0le0
    c2
    cc
    wcel
    c2
    cc0
    wne
    c2
    c1
    wne
    @6
    cc0
    wceq
    2cn
    2ne0
    c1
    c2
    1ne2
    necomi
    c2
    logb1
    mp3an
    #
    breqtrri
    @6
    cc0
    c1
    clt
    @9
    0lt1
    eqbrtri
    pm3.2i
    @1
    @3
    @7
    @4
    @8
    @1
    @2
    @6
    cc0
    cle
    cN
    c1
    c2
    clogb
    oveq2
    #
    breq2d
    @1
    @2
    @6
    c1
    clt
    @10
    breq1d
    anbi12d
    mpbiri
    @0
    @5
    c1
    cN
    cle
    wbr
    #
    cN
    c2
    clt
    wbr
    #
    wa
    #
    @1
    @0
    @3
    @11
    @4
    @12
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
    @3
    @11
    wb
    @14
    @0
    c2
    cz
    wcel
    @14
    2z
    c2
    uzid
    ax-mp
    a1i
    #
    cN
    nnrp
    #
    c2
    cN
    logbge0b
    syl2anc
    @0
    @14
    @15
    @4
    @12
    wb
    @16
    @17
    c2
    cN
    logblt1b
    syl2anc
    anbi12d
    @0
    @13
    cN
    cfl
    cfv
    #
    c1
    wceq
    #
    @1
    @0
    @13
    @11
    cN
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @19
    @0
    @12
    @21
    @11
    @12
    @21
    wb
    @0
    c2
    @20
    cN
    clt
    df-2
    breq2i
    a1i
    anbi2d
    @0
    cN
    cr
    wcel
    c1
    cz
    wcel
    @19
    @22
    wb
    cN
    nnre
    @0
    1zzd
    cN
    c1
    flbi
    syl2anc
    bitr4d
    @0
    @19
    @1
    @0
    @19
    wa
    cN
    @18
    c1
    @0
    cN
    @18
    wceq
    @19
    @0
    @18
    cN
    @0
    cN
    cz
    wcel
    @18
    cN
    wceq
    cN
    nnz
    cN
    flid
    syl
    eqcomd
    adantr
    @0
    @19
    simpr
    eqtrd
    ex
    sylbid
    sylbid
    impbid2
end
