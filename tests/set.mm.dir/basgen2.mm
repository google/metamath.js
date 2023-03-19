include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "dfss3.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "eltg2b.mm"
include "syl.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "biimp3ar.mm"
include "basgen.mm"
include "syld3an3.mm"

theorem basgen2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cJ: class J
  let cC: class C
  let cV: class V

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint V x
  disjoint V y
  assert |- ( ( J e. Top /\ B C_ J /\ A. x e. J A. y e. x E. z e. B ( y e. z /\ z C_ x ) ) -> ( topGen ` B ) = J )

  proof
    cJ
    ctop
    wcel
    #
    cB
    cJ
    wss
    #
    vy
    cv
    vz
    cv
    #
    wcel
    @2
    vx
    cv
    #
    wss
    wa
    vz
    cB
    wrex
    vy
    @3
    wral
    #
    vx
    cJ
    wral
    #
    cJ
    cB
    ctg
    cfv
    #
    wss
    #
    @6
    cJ
    wceq
    @0
    @1
    @7
    @5
    @7
    @3
    @6
    wcel
    #
    vx
    cJ
    wral
    @0
    @1
    wa
    #
    @5
    vx
    cJ
    @6
    dfss3
    @9
    @8
    @4
    vx
    cJ
    @9
    cB
    cvv
    wcel
    #
    @8
    @4
    wb
    @1
    @0
    @10
    cB
    cJ
    ctop
    ssexg
    ancoms
    vy
    vz
    @3
    cB
    cvv
    eltg2b
    syl
    ralbidv
    syl5bb
    biimp3ar
    cB
    cJ
    basgen
    syld3an3
end
