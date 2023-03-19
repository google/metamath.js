include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "sspadd1.mm"
include "3adant3r3.mm"
include "sstr.mm"
include "sylan.mm"
include "ex.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "sspadd2.mm"
include "syl3anc.mm"
include "jcad.mm"

theorem paddssw2
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddssw.a: |- A = ( Atoms ` K )
  assume paddssw.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) ) -> ( ( X .+ Y ) C_ Z -> ( X C_ Z /\ Y C_ Z ) ) )

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
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    wss
    #
    cX
    cZ
    wss
    #
    cY
    cZ
    wss
    #
    @5
    @7
    @8
    @5
    cX
    @6
    wss
    #
    @7
    @8
    @0
    @1
    @2
    @10
    @3
    cA
    cB
    c.pl
    cK
    cX
    cY
    paddssw.a
    paddssw.p
    sspadd1
    3adant3r3
    cX
    @6
    cZ
    sstr
    sylan
    ex
    @5
    @7
    @9
    @5
    cY
    @6
    wss
    #
    @7
    @9
    @5
    @0
    @2
    @1
    @11
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr1
    cA
    cB
    c.pl
    cK
    cY
    cX
    paddssw.a
    paddssw.p
    sspadd2
    syl3anc
    cY
    @6
    cZ
    sstr
    sylan
    ex
    jcad
end
