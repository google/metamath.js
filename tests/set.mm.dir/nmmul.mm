include "cnrg.mm"
include "wcel.mm"
include "cabv.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "eqid.mm"
include "nrgabv.mm"
include "abvmul.mm"
include "syl3an1.mm"

theorem nmmul
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cX: class X
  assume nmmul.x: |- X = ( Base ` R )
  assume nmmul.n: |- N = ( norm ` R )
  assume nmmul.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. NrmRing /\ A e. X /\ B e. X ) -> ( N ` ( A .x. B ) ) = ( ( N ` A ) x. ( N ` B ) ) )

  proof
    cR
    cnrg
    wcel
    cN
    cR
    cabv
    cfv
    #
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    c.x
    co
    cN
    cfv
    cA
    cN
    cfv
    cB
    cN
    cfv
    cmul
    co
    wceq
    @0
    cR
    cN
    nmmul.n
    @0
    eqid
    #
    nrgabv
    @0
    cX
    cR
    c.x
    cN
    cA
    cB
    @1
    nmmul.x
    nmmul.t
    abvmul
    syl3an1
end
