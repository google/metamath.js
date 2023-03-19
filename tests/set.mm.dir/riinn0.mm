include "wss.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ciin.mm"
include "cin.mm"
include "incom.mm"
include "wceq.mm"
include "wrex.mm"
include "r19.2z.mm"
include "ancoms.mm"
include "iinss.mm"
include "syl.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"

theorem riinn0
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cX: class X
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint X x
  disjoint A y
  disjoint x y
  disjoint X y
  disjoint B x
  assert |- ( ( A. x e. X S C_ A /\ X =/= (/) ) -> ( A i^i |^|_ x e. X S ) = |^|_ x e. X S )

  proof
    cS
    cA
    wss
    #
    vx
    cX
    wral
    #
    cX
    c0
    wne
    #
    wa
    #
    cA
    vx
    cX
    cS
    ciin
    #
    cin
    @4
    cA
    cin
    #
    @4
    cA
    @4
    incom
    @3
    @4
    cA
    wss
    #
    @5
    @4
    wceq
    @3
    @0
    vx
    cX
    wrex
    #
    @6
    @2
    @1
    @7
    @0
    vx
    cX
    r19.2z
    ancoms
    vx
    cX
    cS
    cA
    iinss
    syl
    @4
    cA
    df-ss
    sylib
    syl5eq
end
