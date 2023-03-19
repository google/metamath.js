include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "ccatws1cl.mm"
include "ad2ant2r.mm"
include "simpr.mm"
include "adantl.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "lencl.mm"
include "fzonn0p1.mm"
include "syl.mm"
include "ad2antrr.mm"
include "eqcomd.mm"
include "adantr.mm"
include "ccatws1len.mm"
include "oveq2d.mm"
include "3eltr4d.mm"
include "ccats1val1.mm"
include "syl3anc.mm"
include "simpl.mm"
include "eqcom.mm"
include "biimpi.mm"
include "ccats1val2.mm"
include "eqtrd.mm"

theorem ccatw2s1p1
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( W e. Word V /\ ( # ` W ) = N ) /\ ( X e. V /\ Y e. V ) ) -> ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` N ) = X )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    wa
    #
    cN
    cW
    cX
    cs1
    cconcat
    co
    #
    cY
    cs1
    cconcat
    co
    cfv
    #
    cN
    @9
    cfv
    #
    cX
    @8
    @9
    @0
    wcel
    #
    @6
    cN
    cc0
    @9
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @10
    @11
    wceq
    @1
    @5
    @12
    @3
    @6
    cV
    cW
    cX
    ccatws1cl
    ad2ant2r
    @7
    @6
    @4
    @5
    @6
    simpr
    adantl
    @8
    @2
    cc0
    @2
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cN
    @14
    @1
    @2
    @16
    wcel
    #
    @3
    @7
    @1
    @2
    cn0
    wcel
    @17
    cV
    cW
    lencl
    @2
    fzonn0p1
    syl
    ad2antrr
    @4
    cN
    @2
    wceq
    #
    @7
    @4
    @2
    cN
    @1
    @3
    simpr
    eqcomd
    adantr
    @8
    @13
    @15
    cc0
    cfzo
    @1
    @13
    @15
    wceq
    @3
    @7
    cV
    cW
    cX
    ccatws1len
    ad2antrr
    oveq2d
    3eltr4d
    cY
    cN
    cV
    @9
    ccats1val1
    syl3anc
    @8
    @1
    @5
    @18
    @11
    cX
    wceq
    @4
    @1
    @7
    @1
    @3
    simpl
    adantr
    @7
    @5
    @4
    @5
    @6
    simpl
    adantl
    @4
    @18
    @7
    @3
    @18
    @1
    @3
    @18
    @2
    cN
    eqcom
    biimpi
    adantl
    adantr
    cX
    cN
    cV
    cW
    ccats1val2
    syl3anc
    eqtrd
end
