include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "co.mm"
include "cun.mm"
include "w3a.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "simpl.mm"
include "0ss.mm"
include "a1i.mm"
include "simpr.mm"
include "3jca.mm"
include "neirr.mm"
include "intnanr.mm"
include "paddval0.mm"
include "sylancl.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem padd02
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cS: class S
  let cY: class Y
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ X C_ A ) -> ( (/) .+ X ) = X )

  proof
    cK
    cB
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    c0
    cX
    c.pl
    co
    #
    c0
    cX
    cun
    #
    cX
    @2
    @0
    c0
    cA
    wss
    #
    @1
    w3a
    c0
    c0
    wne
    #
    cX
    c0
    wne
    #
    wa
    wn
    @3
    @4
    wceq
    @2
    @0
    @5
    @1
    @0
    @1
    simpl
    @5
    @2
    cA
    0ss
    a1i
    @0
    @1
    simpr
    3jca
    @6
    @7
    c0
    neirr
    intnanr
    cA
    cB
    c.pl
    cK
    c0
    cX
    padd0.a
    padd0.p
    paddval0
    sylancl
    @4
    cX
    c0
    cun
    cX
    c0
    cX
    uncom
    cX
    un0
    eqtri
    syl6eq
end
