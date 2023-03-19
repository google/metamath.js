include "wcel.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "id.mm"
include "eqid.mm"
include "psr1bas2.mm"
include "syl6eleq.mm"

theorem psr1bascl
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  assume psr1rcl.p: |- P = ( PwSer1 ` R )
  assume psr1rcl.b: |- B = ( Base ` P )


  assert |- ( F e. B -> F e. ( Base ` ( 1o mPwSer R ) ) )

  proof
    cF
    cB
    wcel
    #
    cF
    cB
    c1o
    cR
    cmps
    co
    #
    cbs
    cfv
    @0
    id
    cB
    cR
    cP
    @1
    psr1rcl.p
    psr1rcl.b
    @1
    eqid
    psr1bas2
    syl6eleq
end
