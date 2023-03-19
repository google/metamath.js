include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "cs1.mm"
include "clsw.mm"
include "cc0.mm"
include "cfzo.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "hashneq0.mm"
include "cn0.mm"
include "cz.mm"
include "wi.mm"
include "lencl.mm"
include "nn0z.mm"
include "cn.mm"
include "elnnz.mm"
include "fzo0end.mm"
include "sylbir.mm"
include "ex.mm"
include "3syl.mm"
include "sylbird.mm"
include "imp.mm"
include "swrds1.mm"
include "syldan.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "jctir.mm"
include "npcan.mm"
include "eqcomd.mm"
include "adantr.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "lsw.mm"
include "s1eqd.mm"
include "3eqtr4d.mm"

theorem swrdlsw
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( W substr <. ( ( # ` W ) - 1 ) , ( # ` W ) >. ) = <" ( lastS ` W ) "> )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    cW
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @5
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    @5
    cW
    cfv
    #
    cs1
    #
    cW
    @5
    @4
    cop
    #
    csubstr
    co
    cW
    clsw
    cfv
    #
    cs1
    @1
    @2
    @5
    cc0
    @4
    cfzo
    co
    wcel
    #
    @8
    @10
    wceq
    @1
    @2
    @13
    @1
    @2
    cc0
    @4
    clt
    wbr
    #
    @13
    cW
    @0
    hashneq0
    @1
    @4
    cn0
    wcel
    #
    @4
    cz
    wcel
    #
    @14
    @13
    wi
    cV
    cW
    lencl
    #
    @4
    nn0z
    @16
    @14
    @13
    @16
    @14
    wa
    @4
    cn
    wcel
    @13
    @4
    elnnz
    @4
    fzo0end
    sylbir
    ex
    3syl
    sylbird
    imp
    cV
    @5
    cW
    swrds1
    syldan
    @3
    @11
    @7
    cW
    csubstr
    @3
    @4
    @6
    @5
    @1
    @4
    @6
    wceq
    #
    @2
    @1
    @15
    @4
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    wa
    #
    @18
    @17
    @15
    @19
    @20
    @4
    nn0cn
    ax-1cn
    jctir
    @21
    @6
    @4
    @4
    c1
    npcan
    eqcomd
    3syl
    adantr
    opeq2d
    oveq2d
    @3
    @12
    @9
    @1
    @12
    @9
    wceq
    @2
    cW
    @0
    lsw
    adantr
    s1eqd
    3eqtr4d
end
