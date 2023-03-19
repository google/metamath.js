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
include "simpr.mm"
include "0ss.mm"
include "a1i.mm"
include "3jca.mm"
include "neirr.mm"
include "intnan.mm"
include "paddval0.mm"
include "sylancl.mm"
include "un0.mm"
include "syl6eq.mm"

theorem padd01
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


  assert |- ( ( K e. B /\ X C_ A ) -> ( X .+ (/) ) = X )

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
    cX
    c0
    c.pl
    co
    #
    cX
    c0
    cun
    #
    cX
    @2
    @0
    @1
    c0
    cA
    wss
    #
    w3a
    cX
    c0
    wne
    #
    c0
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
    @1
    @5
    @0
    @1
    simpl
    @0
    @1
    simpr
    @5
    @2
    cA
    0ss
    a1i
    3jca
    @7
    @6
    c0
    neirr
    intnan
    cA
    cB
    c.pl
    cK
    cX
    c0
    padd0.a
    padd0.p
    paddval0
    sylancl
    cX
    un0
    syl6eq
end
