include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "clsw.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "lsw.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "sylan9eq.mm"

theorem lsw1
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) = 1 ) -> ( lastS ` W ) = ( W ` 0 ) )

  proof
    cW
    cV
    cword
    #
    wcel
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    cW
    clsw
    cfv
    @1
    c1
    cmin
    co
    #
    cW
    cfv
    cc0
    cW
    cfv
    cW
    @0
    lsw
    @2
    @3
    cc0
    cW
    @2
    @3
    c1
    c1
    cmin
    co
    cc0
    @1
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    sylan9eq
end
