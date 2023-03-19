include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "c1.mm"
include "wceq.mm"
include "s1cl.mm"
include "ccatlen.mm"
include "sylan2.mm"
include "s1len.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem ccatws1lenOLD
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ X e. V ) -> ( # ` ( W ++ <" X "> ) ) = ( ( # ` W ) + 1 ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cW
    cX
    cs1
    #
    cconcat
    co
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    @4
    chash
    cfv
    #
    caddc
    co
    #
    @6
    c1
    caddc
    co
    @2
    @1
    @4
    @0
    wcel
    @5
    @8
    wceq
    cX
    cV
    s1cl
    cV
    cW
    @4
    ccatlen
    sylan2
    @3
    @7
    c1
    @6
    caddc
    @7
    c1
    wceq
    @3
    cX
    s1len
    a1i
    oveq2d
    eqtrd
end
