include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cin.mm"
include "elin.mm"
include "jplem2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "chincli.mm"
include "bitr3d.mm"

theorem jpi
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  assume jp.1: |- S = ( x e. CH |-> ( ( normh ` ( ( projh ` x ) ` u ) ) ^ 2 ) )
  assume jp.2: |- A e. CH
  assume jp.3: |- B e. CH

  disjoint u x
  disjoint A x
  disjoint B x
  assert |- ( ( u e. ~H /\ ( normh ` u ) = 1 ) -> ( ( ( S ` A ) = 1 /\ ( S ` B ) = 1 ) <-> ( S ` ( A i^i B ) ) = 1 ) )

  proof
    vu
    cv
    #
    chil
    wcel
    @0
    cno
    cfv
    c1
    wceq
    wa
    #
    @0
    cA
    cB
    cin
    #
    wcel
    #
    cA
    cS
    cfv
    c1
    wceq
    #
    cB
    cS
    cfv
    c1
    wceq
    #
    wa
    #
    @2
    cS
    cfv
    c1
    wceq
    @3
    @0
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    @1
    @6
    @0
    cA
    cB
    elin
    @1
    @7
    @4
    @8
    @5
    vx
    vu
    cA
    cS
    jp.1
    jp.2
    jplem2
    vx
    vu
    cB
    cS
    jp.1
    jp.3
    jplem2
    anbi12d
    syl5bb
    vx
    vu
    @2
    cS
    jp.1
    cA
    cB
    jp.2
    jp.3
    chincli
    jplem2
    bitr3d
end
