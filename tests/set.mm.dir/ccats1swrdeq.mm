include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "cmin.mm"
include "3ad2ant3.mm"
include "cn0.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "eqtr2d.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "c0.mm"
include "wne.mm"
include "simp2.mm"
include "clt.mm"
include "wbr.mm"
include "nn0p1gt0.mm"
include "syl.mm"
include "wb.mm"
include "breq2.mm"
include "mpbird.mm"
include "hashneq0.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "swrdccatwrd.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "adantr.mm"
include "ex.mm"

theorem ccats1swrdeq
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ U e. Word V /\ ( # ` U ) = ( ( # ` W ) + 1 ) ) -> ( W = ( U substr <. 0 , ( # ` W ) >. ) -> U = ( W ++ <" ( lastS ` U ) "> ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cU
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cW
    cU
    cc0
    @4
    cop
    #
    csubstr
    co
    #
    wceq
    #
    cU
    cW
    cU
    clsw
    cfv
    cs1
    #
    cconcat
    co
    #
    wceq
    @7
    @10
    wa
    @12
    @9
    @11
    cconcat
    co
    #
    cU
    @10
    @12
    @13
    wceq
    @7
    cW
    @9
    @11
    cconcat
    oveq1
    adantl
    @7
    @13
    cU
    wceq
    @10
    @7
    @13
    cU
    cc0
    @3
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @11
    cconcat
    co
    #
    cU
    @7
    @9
    @16
    @11
    cconcat
    @7
    @8
    @15
    cU
    csubstr
    @7
    @4
    @14
    cc0
    @7
    @14
    @5
    c1
    cmin
    co
    #
    @4
    @6
    @1
    @14
    @18
    wceq
    @2
    @3
    @5
    c1
    cmin
    oveq1
    3ad2ant3
    @1
    @2
    @18
    @4
    wceq
    #
    @6
    @1
    @4
    cn0
    wcel
    #
    @4
    cc
    wcel
    @19
    cV
    cW
    lencl
    #
    @4
    nn0cn
    @4
    pncan1
    3syl
    3ad2ant1
    eqtr2d
    opeq2d
    oveq2d
    oveq1d
    @7
    @2
    cU
    c0
    wne
    #
    @17
    cU
    wceq
    @1
    @2
    @6
    simp2
    @7
    cc0
    @3
    clt
    wbr
    #
    @22
    @7
    @23
    cc0
    @5
    clt
    wbr
    #
    @1
    @2
    @24
    @6
    @1
    @20
    @24
    @21
    @4
    nn0p1gt0
    syl
    3ad2ant1
    @6
    @1
    @23
    @24
    wb
    @2
    @3
    @5
    cc0
    clt
    breq2
    3ad2ant3
    mpbird
    @2
    @1
    @23
    @22
    wb
    @6
    cU
    @0
    hashneq0
    3ad2ant2
    mpbid
    cV
    cU
    swrdccatwrd
    syl2anc
    eqtrd
    adantr
    eqtr2d
    ex
end
