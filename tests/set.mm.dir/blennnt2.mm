include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cblen.mm"
include "cfv.mm"
include "clogb.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "2nn.mm"
include "a1i.mm"
include "id.mm"
include "nnmulcld.mm"
include "blennn.mm"
include "syl.mm"
include "cc.mm"
include "2cn.mm"
include "nncn.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "cc0.mm"
include "cpr.mm"
include "cdif.mm"
include "crp.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "eluz2cnn0n1.mm"
include "mp1i.mm"
include "nnrp.mm"
include "2rp.mm"
include "relogbmul.mm"
include "syl12anc.mm"
include "wne.mm"
include "w3a.mm"
include "2ne0.mm"
include "1ne2.mm"
include "necomi.mm"
include "3pm3.2i.mm"
include "logbid1.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "cr.mm"
include "relogbcl.mm"
include "syl3anc.mm"
include "1zzd.mm"
include "fladdz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqcomd.mm"

theorem blennnt2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( #b ` ( 2 x. N ) ) = ( ( #b ` N ) + 1 ) )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cmul
    co
    #
    cblen
    cfv
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
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    c1
    caddc
    co
    #
    c1
    caddc
    co
    cN
    cblen
    cfv
    #
    c1
    caddc
    co
    @0
    @1
    cn
    wcel
    @2
    @5
    wceq
    @0
    c2
    cN
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @0
    id
    nnmulcld
    @1
    blennn
    syl
    @0
    @4
    @7
    c1
    caddc
    @0
    @4
    @6
    c1
    caddc
    co
    #
    cfl
    cfv
    #
    @7
    @0
    @3
    @9
    cfl
    @0
    @3
    c2
    cN
    c2
    cmul
    co
    #
    clogb
    co
    #
    @6
    c2
    c2
    clogb
    co
    #
    caddc
    co
    #
    @9
    @0
    @1
    @11
    c2
    clogb
    @0
    c2
    cN
    c2
    cc
    wcel
    #
    @0
    2cn
    a1i
    cN
    nncn
    mulcomd
    oveq2d
    @0
    c2
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cN
    crp
    wcel
    #
    c2
    crp
    wcel
    #
    @12
    @14
    wceq
    c2
    c2
    cuz
    cfv
    wcel
    #
    @16
    @0
    c2
    cz
    wcel
    @19
    2z
    c2
    uzid
    ax-mp
    c2
    eluz2cnn0n1
    mp1i
    cN
    nnrp
    #
    @18
    @0
    2rp
    a1i
    #
    cN
    c2
    c2
    relogbmul
    syl12anc
    @0
    @13
    c1
    @6
    caddc
    @15
    c2
    cc0
    wne
    #
    c2
    c1
    wne
    #
    w3a
    @13
    c1
    wceq
    @0
    @15
    @22
    @23
    2cn
    2ne0
    c1
    c2
    1ne2
    necomi
    #
    3pm3.2i
    c2
    logbid1
    mp1i
    oveq2d
    3eqtrd
    fveq2d
    @0
    @6
    cr
    wcel
    #
    c1
    cz
    wcel
    @10
    @7
    wceq
    @0
    @18
    @17
    @23
    @25
    @21
    @20
    @23
    @0
    @24
    a1i
    c2
    cN
    relogbcl
    syl3anc
    @0
    1zzd
    @6
    c1
    fladdz
    syl2anc
    eqtrd
    oveq1d
    @0
    @7
    @8
    c1
    caddc
    @0
    @8
    @7
    cN
    blennn
    eqcomd
    oveq1d
    3eqtrd
end
