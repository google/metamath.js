include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "wa.mm"
include "clogb.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cblen.mm"
include "cmin.mm"
include "crp.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wne.mm"
include "2rp.mm"
include "1ne2.mm"
include "necomi.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "nnrp.mm"
include "adantr.mm"
include "relogbdivb.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cr.mm"
include "cz.mm"
include "a1i.mm"
include "relogbcl.mm"
include "syl3anc.mm"
include "1zzd.mm"
include "jca.mm"
include "flsubz.mm"
include "syl.mm"
include "cc.mm"
include "flcld.mm"
include "zcnd.mm"
include "npcan1.mm"
include "3eqtrd.mm"
include "nn0enne.mm"
include "biimpa.mm"
include "blennn.mm"
include "3eqtr4rd.mm"

theorem blennn0e2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( N / 2 ) e. NN0 ) -> ( #b ` N ) = ( ( #b ` ( N / 2 ) ) + 1 ) )

  proof
    cN
    cn
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
    c2
    @1
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
    caddc
    co
    #
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
    @1
    cblen
    cfv
    #
    c1
    caddc
    co
    #
    cN
    cblen
    cfv
    #
    @3
    @6
    @9
    c1
    caddc
    @3
    @6
    @8
    c1
    cmin
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    @9
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @9
    @3
    @5
    @15
    c1
    caddc
    @3
    @4
    @14
    cfl
    @3
    c2
    crp
    c1
    csn
    cdif
    wcel
    #
    cN
    crp
    wcel
    #
    @4
    @14
    wceq
    @18
    c2
    crp
    wcel
    #
    c2
    c1
    wne
    #
    2rp
    c1
    c2
    1ne2
    necomi
    #
    c2
    crp
    c1
    eldifsn
    mpbir2an
    @0
    @19
    @2
    cN
    nnrp
    #
    adantr
    cN
    c2
    relogbdivb
    sylancr
    fveq2d
    oveq1d
    @3
    @15
    @16
    c1
    caddc
    @3
    @8
    cr
    wcel
    #
    c1
    cz
    wcel
    #
    wa
    #
    @15
    @16
    wceq
    @0
    @26
    @2
    @0
    @24
    @25
    @0
    @20
    @19
    @21
    @24
    @20
    @0
    2rp
    a1i
    @23
    @21
    @0
    @22
    a1i
    c2
    cN
    relogbcl
    syl3anc
    #
    @0
    1zzd
    jca
    adantr
    @8
    c1
    flsubz
    syl
    oveq1d
    @0
    @17
    @9
    wceq
    #
    @2
    @0
    @9
    cc
    wcel
    @28
    @0
    @9
    @0
    @8
    @27
    flcld
    zcnd
    @9
    npcan1
    syl
    adantr
    3eqtrd
    oveq1d
    @3
    @1
    cn
    wcel
    #
    @12
    @7
    wceq
    @0
    @2
    @29
    cN
    nn0enne
    biimpa
    @29
    @11
    @6
    c1
    caddc
    @1
    blennn
    oveq1d
    syl
    @0
    @13
    @10
    wceq
    @2
    cN
    blennn
    adantr
    3eqtr4rd
end
