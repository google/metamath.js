include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfa.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cmo.mm"
include "cneg.mm"
include "wceq.mm"
include "wilth.mm"
include "cc0.mm"
include "cn.mm"
include "cz.mm"
include "wb.mm"
include "eluz2nn.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "faccld.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "dvdsval3.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "cc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "jca.mm"
include "adantr.mm"
include "subneg.mm"
include "breqtrrd.mm"
include "w3a.mm"
include "neg1z.mm"
include "a1i.mm"
include "3jca.mm"
include "moddvds.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"
include "sylbi.mm"

theorem wilthimp
  let cP: class P


  assert |- ( P e. Prime -> ( ( ! ` ( P - 1 ) ) mod P ) = ( -u 1 mod P ) )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    wcel
    #
    cP
    cP
    c1
    cmin
    co
    #
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    wa
    @2
    cP
    cmo
    co
    c1
    cneg
    #
    cP
    cmo
    co
    wceq
    #
    cP
    wilth
    @0
    @4
    @6
    @0
    @4
    @3
    cP
    cmo
    co
    cc0
    wceq
    #
    @6
    @0
    cP
    cn
    wcel
    #
    @3
    cz
    wcel
    @4
    @7
    wb
    cP
    eluz2nn
    #
    @0
    @2
    @0
    @2
    @0
    @1
    @0
    @8
    @1
    cn0
    wcel
    @9
    cP
    nnm1nn0
    syl
    faccld
    #
    nnzd
    #
    peano2zd
    cP
    @3
    dvdsval3
    syl2anc
    #
    @0
    @7
    @6
    @0
    @7
    wa
    #
    @6
    cP
    @2
    @5
    cmin
    co
    #
    cdvds
    wbr
    #
    @13
    cP
    @3
    @14
    cdvds
    @0
    @4
    @7
    @12
    biimpar
    @13
    @2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    wa
    #
    @14
    @3
    wceq
    @0
    @18
    @7
    @0
    @16
    @17
    @0
    @2
    @10
    nncnd
    @0
    1cnd
    jca
    adantr
    @2
    c1
    subneg
    syl
    breqtrrd
    @13
    @8
    @2
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    w3a
    #
    @6
    @15
    wb
    @0
    @21
    @7
    @0
    @8
    @19
    @20
    @9
    @11
    @20
    @0
    neg1z
    a1i
    3jca
    adantr
    @2
    @5
    cP
    moddvds
    syl
    mpbird
    ex
    sylbid
    imp
    sylbi
end
