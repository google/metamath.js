include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cpfx.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "ccats1pfxeq.mm"
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
include "pfxccatid.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "ex.mm"
include "impbid.mm"

theorem ccats1pfxeqbi
  let cU: class U
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ U e. Word V /\ ( # ` U ) = ( ( # ` W ) + 1 ) ) -> ( W = ( U prefix ( # ` W ) ) <-> U = ( W ++ <" ( lastS ` U ) "> ) ) )

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
    @3
    cpfx
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
    ccats1pfxeq
    @6
    @12
    @8
    @6
    @12
    cW
    @11
    @3
    cpfx
    co
    #
    @7
    @6
    @1
    @10
    @0
    wcel
    #
    @3
    @3
    wceq
    #
    cW
    @13
    wceq
    @1
    @2
    @5
    simp1
    @6
    @9
    cV
    @6
    @4
    cn
    wcel
    #
    @2
    @5
    wa
    @9
    cV
    wcel
    @1
    @2
    @16
    @5
    @1
    @3
    cn0
    wcel
    @16
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
    @14
    @15
    w3a
    @13
    cW
    cW
    @10
    @3
    cV
    pfxccatid
    eqcomd
    syl3anc
    @12
    @7
    @13
    cU
    @11
    @3
    cpfx
    oveq1
    eqcomd
    sylan9eq
    ex
    impbid
end
