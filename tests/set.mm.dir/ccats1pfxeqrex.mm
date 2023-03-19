include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "clsw.mm"
include "cpfx.mm"
include "cs1.mm"
include "cconcat.mm"
include "cv.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "simp2.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "cn.mm"
include "lencl.mm"
include "3ad2ant1.mm"
include "nn0p1nn.mm"
include "nngt0.mm"
include "3syl.mm"
include "wb.mm"
include "breq2.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "hashgt0n0.mm"
include "syl2anc.mm"
include "lswcl.mm"
include "ccats1pfxeq.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl6an.mm"

theorem ccats1pfxeqrex
  let cU: class U
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x

  disjoint U s
  disjoint V s
  disjoint W s
  disjoint k x
  assert |- ( ( W e. Word V /\ U e. Word V /\ ( # ` U ) = ( ( # ` W ) + 1 ) ) -> ( W = ( U prefix ( # ` W ) ) -> E. s e. V U = ( W ++ <" s "> ) ) )

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
    cU
    clsw
    cfv
    #
    cV
    wcel
    #
    cW
    cU
    @4
    cpfx
    co
    wceq
    cU
    cW
    @8
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    cU
    cW
    vs
    cv
    #
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    vs
    cV
    wrex
    @7
    @2
    cU
    c0
    wne
    #
    @9
    @1
    @2
    @6
    simp2
    #
    @7
    @2
    cc0
    @3
    clt
    wbr
    #
    @17
    @18
    @7
    @19
    cc0
    @5
    clt
    wbr
    #
    @7
    @4
    cn0
    wcel
    #
    @5
    cn
    wcel
    @20
    @1
    @2
    @21
    @6
    cV
    cW
    lencl
    3ad2ant1
    @4
    nn0p1nn
    @5
    nngt0
    3syl
    @6
    @1
    @19
    @20
    wb
    @2
    @3
    @5
    cc0
    clt
    breq2
    3ad2ant3
    mpbird
    cU
    @0
    hashgt0n0
    syl2anc
    cV
    cU
    lswcl
    syl2anc
    cU
    cV
    cW
    ccats1pfxeq
    @16
    @12
    vs
    @8
    cV
    @13
    @8
    wceq
    #
    @15
    @11
    cU
    @22
    @14
    @10
    cW
    cconcat
    @13
    @8
    s1eq
    oveq2d
    eqeq2d
    rspcev
    syl6an
end
