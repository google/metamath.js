include "cuni.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "wb.mm"
include "wal.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "w3a.mm"
include "wa.mm"
include "ttukey2g.mm"
include "simpr.mm"
include "reximi.mm"
include "syl.mm"
include "3exp.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3imp.mm"

theorem ttukeyg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( U. A e. dom card /\ A =/= (/) /\ A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) ) -> E. x e. A A. y e. A -. x C. y )

  proof
    cA
    cuni
    ccrd
    cdm
    wcel
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
    cA
    wcel
    @2
    cpw
    cfn
    cin
    cA
    wss
    wb
    vx
    wal
    #
    @2
    vy
    cv
    wpss
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @1
    vz
    cv
    #
    cA
    wcel
    #
    vz
    wex
    @0
    @3
    @5
    wi
    #
    vz
    cA
    n0
    @0
    @7
    @8
    vz
    @0
    @7
    @3
    @5
    @0
    @7
    @3
    w3a
    @6
    @2
    wss
    #
    @4
    wa
    #
    vx
    cA
    wrex
    @5
    vx
    vy
    cA
    @6
    ttukey2g
    @10
    @4
    vx
    cA
    @9
    @4
    simpr
    reximi
    syl
    3exp
    exlimdv
    syl5bi
    3imp
end
