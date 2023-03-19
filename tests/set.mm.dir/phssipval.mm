include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cphl.mm"
include "wa.mm"
include "ssipeq.mm"
include "oveqd.mm"
include "ad2antlr.mm"

theorem phssipval
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let c.xi: class .,
  let cW: class W
  let cX: class X
  assume ssipeq.x: |- X = ( W |`s U )
  assume ssipeq.i: |- ., = ( .i ` W )
  assume ssipeq.p: |- P = ( .i ` X )
  assume ssipeq.s: |- S = ( LSubSp ` W )


  assert |- ( ( ( W e. PreHil /\ U e. S ) /\ ( A e. U /\ B e. U ) ) -> ( A P B ) = ( A ., B ) )

  proof
    cU
    cS
    wcel
    #
    cA
    cB
    cP
    co
    cA
    cB
    c.xi
    co
    wceq
    cW
    cphl
    wcel
    cA
    cU
    wcel
    cB
    cU
    wcel
    wa
    @0
    cP
    c.xi
    cA
    cB
    cP
    cS
    cU
    c.xi
    cW
    cX
    ssipeq.x
    ssipeq.i
    ssipeq.p
    ssipeq
    oveqd
    ad2antlr
end
