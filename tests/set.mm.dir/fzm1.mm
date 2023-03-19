include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wo.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "elfz1eq.mm"
include "syl6bir.mm"
include "olc.mm"
include "syl6.mm"
include "adantl.mm"
include "c0.mm"
include "noel.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "eluzelz.mm"
include "adantr.mm"
include "zred.mm"
include "ltm1d.mm"
include "breq2.mm"
include "mpbid.mm"
include "eluzel2.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "fzn.mm"
include "syl2anc.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "eluzfz2.mm"
include "ad2antrr.mm"
include "eleq1.mm"
include "mpbird.mm"
include "ex.mm"
include "jaod.mm"
include "impbid.mm"
include "caddc.mm"
include "elfzp1.mm"
include "cc.mm"
include "zcnd.mm"
include "npcan1.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "orbi2d.mm"
include "3bitr3d.mm"
include "uzm1.mm"
include "mpjaodan.mm"

theorem fzm1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( K e. ( M ... N ) <-> ( K e. ( M ... ( N - 1 ) ) \/ K = N ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cM
    wceq
    #
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cK
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    cK
    cN
    wceq
    #
    wo
    #
    wb
    @5
    @0
    wcel
    #
    @1
    @2
    wa
    #
    @4
    @9
    @2
    @4
    @9
    wi
    @1
    @2
    @4
    @8
    @9
    @2
    @4
    cK
    cN
    cN
    cfz
    co
    #
    wcel
    @8
    @2
    @12
    @3
    cK
    cN
    cM
    cN
    cfz
    oveq1
    eleq2d
    cK
    cN
    elfz1eq
    syl6bir
    @8
    @7
    olc
    syl6
    adantl
    @11
    @7
    @4
    @8
    @11
    @7
    @4
    @11
    @7
    cK
    c0
    wcel
    cK
    noel
    @11
    @6
    c0
    cK
    @11
    @5
    cM
    clt
    wbr
    #
    @6
    c0
    wceq
    #
    @11
    @5
    cN
    clt
    wbr
    #
    @13
    @11
    cN
    @11
    cN
    @1
    cN
    cz
    wcel
    #
    @2
    cM
    cN
    eluzelz
    #
    adantr
    #
    zred
    ltm1d
    @2
    @15
    @13
    wb
    @1
    cN
    cM
    @5
    clt
    breq2
    adantl
    mpbid
    @11
    cM
    cz
    wcel
    #
    @5
    cz
    wcel
    @13
    @14
    wb
    @1
    @19
    @2
    cM
    cN
    eluzel2
    adantr
    @11
    cN
    c1
    @18
    @11
    1zzd
    zsubcld
    cM
    @5
    fzn
    syl2anc
    mpbid
    eleq2d
    mtbiri
    pm2.21d
    @11
    @8
    @4
    @11
    @8
    wa
    @4
    cN
    @3
    wcel
    #
    @1
    @20
    @2
    @8
    cM
    cN
    eluzfz2
    ad2antrr
    @8
    @4
    @20
    wb
    @11
    cK
    cN
    @3
    eleq1
    adantl
    mpbird
    ex
    jaod
    impbid
    @1
    @10
    wa
    #
    cK
    cM
    @5
    c1
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    @7
    cK
    @22
    wceq
    #
    wo
    #
    @4
    @9
    @10
    @24
    @26
    wb
    @1
    cK
    cM
    @5
    elfzp1
    adantl
    @21
    @23
    @3
    cK
    @21
    @22
    cN
    cM
    cfz
    @21
    cN
    cc
    wcel
    @22
    cN
    wceq
    @21
    cN
    @1
    @16
    @10
    @17
    adantr
    zcnd
    cN
    npcan1
    syl
    #
    oveq2d
    eleq2d
    @21
    @25
    @8
    @7
    @21
    @22
    cN
    cK
    @27
    eqeq2d
    orbi2d
    3bitr3d
    cM
    cN
    uzm1
    mpjaodan
end
