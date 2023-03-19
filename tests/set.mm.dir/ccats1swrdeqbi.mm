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
include "ccats1swrdeq.mm"
include "simp1.mm"
include "cn.mm"
include "wa.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "lswlgt0cl.mm"
include "syl2anc.mm"
include "s1cld.mm"
include "eqidd.mm"
include "swrdccatid.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "ex.mm"
include "impbid.mm"

theorem ccats1swrdeqbi
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ U e. Word V /\ ( # ` U ) = ( ( # ` W ) + 1 ) ) -> ( W = ( U substr <. 0 , ( # ` W ) >. ) <-> U = ( W ++ <" ( lastS ` U ) "> ) ) )

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
    @3
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
    #
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    cU
    cV
    cW
    ccats1swrdeq
    @6
    @13
    @9
    @6
    @13
    cW
    @12
    @7
    csubstr
    co
    #
    @8
    @6
    @1
    @11
    @0
    wcel
    #
    @3
    @3
    wceq
    #
    cW
    @14
    wceq
    @1
    @2
    @5
    simp1
    @6
    @10
    cV
    @6
    @4
    cn
    wcel
    #
    @2
    @5
    wa
    @10
    cV
    wcel
    @1
    @2
    @17
    @5
    @1
    @3
    cn0
    wcel
    @17
    cV
    cW
    lencl
    @3
    nn0p1nn
    syl
    3ad2ant1
    @1
    @2
    @5
    3simpc
    @4
    cV
    cU
    lswlgt0cl
    syl2anc
    s1cld
    @6
    @3
    eqidd
    @1
    @15
    @16
    w3a
    @14
    cW
    cW
    @11
    @3
    cV
    swrdccatid
    eqcomd
    syl3anc
    @13
    @8
    @14
    cU
    @12
    @7
    csubstr
    oveq1
    eqcomd
    sylan9eq
    ex
    impbid
end
