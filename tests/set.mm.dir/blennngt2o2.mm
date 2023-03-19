include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cn0.mm"
include "wa.mm"
include "cmin.mm"
include "clogb.mm"
include "cfl.mm"
include "cblen.mm"
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
include "uz2m1nn.mm"
include "nnrpd.mm"
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
include "1z.mm"
include "jctir.mm"
include "flsubz.mm"
include "syl.mm"
include "cc.mm"
include "flcld.mm"
include "zcnd.mm"
include "npcan1.mm"
include "cn.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "eluz2nn.mm"
include "peano2nnd.mm"
include "nnred.mm"
include "2re.mm"
include "eluzge2nn0.mm"
include "nn0p1gt0.mm"
include "2pos.mm"
include "divgt0d.mm"
include "nn0z.mm"
include "anim12ci.mm"
include "elnnz.mm"
include "sylibr.mm"
include "nnolog2flm1.mm"
include "syldan.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "nno.mm"
include "blennn.mm"
include "3eqtr4rd.mm"

theorem blennngt2o2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( #b ` N ) = ( ( #b ` ( ( N - 1 ) / 2 ) ) + 1 ) )

  proof
    cN
    c2
    cuz
    cfv
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
    c2
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
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
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    @6
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
    @4
    @9
    @11
    c1
    caddc
    @4
    @9
    c2
    @5
    clogb
    co
    #
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
    @16
    cfl
    cfv
    #
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @11
    @4
    @8
    @18
    c1
    caddc
    @4
    @7
    @17
    cfl
    @4
    c2
    crp
    c1
    csn
    cdif
    wcel
    #
    @5
    crp
    wcel
    #
    @7
    @17
    wceq
    @22
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
    @23
    @3
    @0
    @5
    cN
    uz2m1nn
    nnrpd
    #
    adantr
    @5
    c2
    relogbdivb
    sylancr
    fveq2d
    oveq1d
    @4
    @18
    @20
    c1
    caddc
    @4
    @16
    cr
    wcel
    #
    c1
    cz
    wcel
    #
    wa
    #
    @18
    @20
    wceq
    @0
    @30
    @3
    @0
    @28
    @29
    @0
    @24
    @23
    @25
    @28
    @24
    @0
    2rp
    a1i
    @27
    @25
    @0
    @26
    a1i
    c2
    @5
    relogbcl
    syl3anc
    #
    1z
    jctir
    adantr
    @16
    c1
    flsubz
    syl
    oveq1d
    @4
    @21
    @19
    @11
    @0
    @21
    @19
    wceq
    #
    @3
    @0
    @19
    cc
    wcel
    @32
    @0
    @19
    @0
    @16
    @31
    flcld
    zcnd
    @19
    npcan1
    syl
    adantr
    @0
    @3
    @2
    cn
    wcel
    #
    @11
    @19
    wceq
    @4
    @2
    cz
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    wa
    @33
    @0
    @35
    @3
    @34
    @0
    @1
    c2
    @0
    @1
    @0
    cN
    cN
    eluz2nn
    #
    peano2nnd
    nnred
    c2
    cr
    wcel
    @0
    2re
    a1i
    @0
    cN
    cn0
    wcel
    cc0
    @1
    clt
    wbr
    cN
    eluzge2nn0
    cN
    nn0p1gt0
    syl
    cc0
    c2
    clt
    wbr
    @0
    2pos
    a1i
    divgt0d
    @2
    nn0z
    anim12ci
    @2
    elnnz
    sylibr
    cN
    nnolog2flm1
    syldan
    eqtr4d
    3eqtrd
    oveq1d
    @4
    @6
    cn
    wcel
    #
    @14
    @10
    wceq
    cN
    nno
    @37
    @13
    @9
    c1
    caddc
    @6
    blennn
    oveq1d
    syl
    @0
    @15
    @12
    wceq
    #
    @3
    @0
    cN
    cn
    wcel
    @38
    @36
    cN
    blennn
    syl
    adantr
    3eqtr4rd
end
