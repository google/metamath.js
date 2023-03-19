include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wi.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "psubssat.mm"
include "3ad2antr3.mm"
include "paddssw1.mm"
include "syl13anc.mm"
include "wceq.mm"
include "paddidm.mm"
include "sseq2d.mm"
include "sylibd.mm"
include "paddssw2.mm"
include "impbid.mm"

theorem paddss
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume paddss.a: |- A = ( Atoms ` K )
  assume paddss.s: |- S = ( PSubSp ` K )
  assume paddss.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ ( X C_ A /\ Y C_ A /\ Z e. S ) ) -> ( ( X C_ Z /\ Y C_ Z ) <-> ( X .+ Y ) C_ Z ) )

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
    cS
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cZ
    wss
    cY
    cZ
    wss
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
    @5
    @6
    @7
    cZ
    cZ
    c.pl
    co
    #
    wss
    #
    @8
    @5
    @0
    @1
    @2
    cZ
    cA
    wss
    #
    @6
    @10
    wi
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @3
    @11
    @2
    cA
    cB
    cS
    cK
    cZ
    paddss.a
    paddss.s
    psubssat
    3ad2antr3
    #
    cA
    cB
    c.pl
    cK
    cX
    cY
    cZ
    paddss.a
    paddss.p
    paddssw1
    syl13anc
    @5
    @9
    cZ
    @7
    @0
    @1
    @3
    @9
    cZ
    wceq
    @2
    cB
    c.pl
    cS
    cK
    cZ
    paddss.s
    paddss.p
    paddidm
    3ad2antr3
    sseq2d
    sylibd
    @5
    @0
    @1
    @2
    @11
    @8
    @6
    wi
    @12
    @13
    @14
    @15
    cA
    cB
    c.pl
    cK
    cX
    cY
    cZ
    paddss.a
    paddss.p
    paddssw2
    syl13anc
    impbid
end
