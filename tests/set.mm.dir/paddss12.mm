include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "simpl1.mm"
include "simpl2.mm"
include "sstr.mm"
include "ancoms.mm"
include "ad2ant2l.mm"
include "3adantl1.mm"
include "3jca.mm"
include "simprl.mm"
include "paddss1.mm"
include "sylc.mm"
include "wi.mm"
include "paddss2.mm"
include "3com23.mm"
include "imp.mm"
include "adantrl.mm"
include "sstrd.mm"
include "ex.mm"

theorem paddss12
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cS: class S
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ Y C_ A /\ W C_ A ) -> ( ( X C_ Y /\ Z C_ W ) -> ( X .+ Z ) C_ ( Y .+ W ) ) )

  proof
    cK
    cB
    wcel
    #
    cY
    cA
    wss
    #
    cW
    cA
    wss
    #
    w3a
    #
    cX
    cY
    wss
    #
    cZ
    cW
    wss
    #
    wa
    #
    cX
    cZ
    c.pl
    co
    #
    cY
    cW
    c.pl
    co
    #
    wss
    @3
    @6
    wa
    #
    @7
    cY
    cZ
    c.pl
    co
    #
    @8
    @9
    @0
    @1
    cZ
    cA
    wss
    #
    w3a
    @4
    @7
    @10
    wss
    @9
    @0
    @1
    @11
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl2
    @1
    @2
    @6
    @11
    @0
    @2
    @5
    @11
    @1
    @4
    @5
    @2
    @11
    cZ
    cW
    cA
    sstr
    ancoms
    ad2ant2l
    3adantl1
    3jca
    @3
    @4
    @5
    simprl
    cA
    cB
    c.pl
    cK
    cX
    cY
    cZ
    padd0.a
    padd0.p
    paddss1
    sylc
    @3
    @5
    @10
    @8
    wss
    #
    @4
    @3
    @5
    @12
    @0
    @2
    @1
    @5
    @12
    wi
    cA
    cB
    c.pl
    cK
    cZ
    cW
    cY
    padd0.a
    padd0.p
    paddss2
    3com23
    imp
    adantrl
    sstrd
    ex
end
