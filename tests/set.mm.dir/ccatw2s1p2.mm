include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "ccatws1cl.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "ccatws1len.mm"
include "ad2antrr.mm"
include "oveq1.mm"
include "ad2antlr.mm"
include "eqtr2d.mm"
include "ccats1val2.mm"
include "syl3anc.mm"

theorem ccatw2s1p2
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( W e. Word V /\ ( # ` W ) = N ) /\ ( X e. V /\ Y e. V ) ) -> ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` ( N + 1 ) ) = Y )

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
    cW
    cX
    cs1
    cconcat
    co
    #
    @0
    wcel
    #
    @6
    cN
    c1
    caddc
    co
    #
    @9
    chash
    cfv
    #
    wceq
    @11
    @9
    cY
    cs1
    cconcat
    co
    cfv
    cY
    wceq
    @1
    @5
    @10
    @3
    @6
    cV
    cW
    cX
    ccatws1cl
    ad2ant2r
    @4
    @5
    @6
    simprr
    @8
    @12
    @2
    c1
    caddc
    co
    #
    @11
    @1
    @12
    @13
    wceq
    @3
    @7
    cV
    cW
    cX
    ccatws1len
    ad2antrr
    @3
    @13
    @11
    wceq
    @1
    @7
    @2
    cN
    c1
    caddc
    oveq1
    ad2antlr
    eqtr2d
    cY
    @11
    cV
    @9
    ccats1val2
    syl3anc
end
