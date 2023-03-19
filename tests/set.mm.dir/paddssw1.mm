include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wi.mm"
include "simpl.mm"
include "simpr3.mm"
include "paddss12.mm"
include "syl3anc.mm"

theorem paddssw1
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddssw.a: |- A = ( Atoms ` K )
  assume paddssw.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) ) -> ( ( X C_ Z /\ Y C_ Z ) -> ( X .+ Y ) C_ ( Z .+ Z ) ) )

  proof
    cK
    cB
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    cZ
    cA
    wss
    #
    w3a
    #
    wa
    @0
    @3
    @3
    cX
    cZ
    wss
    cY
    cZ
    wss
    wa
    cX
    cY
    c.pl
    co
    cZ
    cZ
    c.pl
    co
    wss
    wi
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr3
    #
    @5
    cA
    cB
    c.pl
    cK
    cZ
    cX
    cZ
    cY
    paddssw.a
    paddssw.p
    paddss12
    syl3anc
end
