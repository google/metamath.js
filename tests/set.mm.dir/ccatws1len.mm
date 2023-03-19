include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "c1.mm"
include "cvv.mm"
include "wceq.mm"
include "wrdv.mm"
include "s1cli.mm"
include "ccatlen.mm"
include "sylancl.mm"
include "s1len.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem ccatws1len
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( W e. Word V -> ( # ` ( W ++ <" X "> ) ) = ( ( # ` W ) + 1 ) )

  proof
    cW
    cV
    cword
    wcel
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
    @1
    chash
    cfv
    #
    caddc
    co
    #
    @3
    c1
    caddc
    co
    @0
    cW
    cvv
    cword
    #
    wcel
    @1
    @6
    wcel
    @2
    @5
    wceq
    cV
    cW
    wrdv
    cX
    s1cli
    cvv
    cW
    @1
    ccatlen
    sylancl
    @0
    @4
    c1
    @3
    caddc
    @4
    c1
    wceq
    @0
    cX
    s1len
    a1i
    oveq2d
    eqtrd
end
