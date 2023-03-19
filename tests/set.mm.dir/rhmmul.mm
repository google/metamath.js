include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "wceq.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mhmlin.mm"
include "syl3an1.mm"

theorem rhmmul
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cX: class X
  assume rhmmul.x: |- X = ( Base ` R )
  assume rhmmul.m: |- .x. = ( .r ` R )
  assume rhmmul.n: |- .X. = ( .r ` S )


  assert |- ( ( F e. ( R RingHom S ) /\ A e. X /\ B e. X ) -> ( F ` ( A .x. B ) ) = ( ( F ` A ) .X. ( F ` B ) ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    cF
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
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
    cF
    cfv
    cA
    cF
    cfv
    cB
    cF
    cfv
    c.xp
    co
    wceq
    cR
    cS
    cF
    @0
    @1
    @0
    eqid
    #
    @1
    eqid
    #
    rhmmhm
    cX
    c.x
    c.xp
    @0
    @1
    cF
    cA
    cB
    cX
    cR
    @0
    @2
    rhmmul.x
    mgpbas
    cR
    c.x
    @0
    @2
    rhmmul.m
    mgpplusg
    cS
    c.xp
    @1
    @3
    rhmmul.n
    mgpplusg
    mhmlin
    syl3an1
end
