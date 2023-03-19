include "cv.mm"
include "cin.mm"
include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "wral.mm"
include "ctb.mm"
include "wceq.mm"
include "ineq1.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "raleqbi1dv.mm"
include "df-bases.mm"
include "elab2g.mm"

theorem isbasisg
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( B e. C -> ( B e. TopBases <-> A. x e. B A. y e. B ( x i^i y ) C_ U. ( B i^i ~P ( x i^i y ) ) ) )

  proof
    vx
    cv
    vy
    cv
    cin
    #
    vz
    cv
    #
    @0
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    @0
    cB
    @2
    cin
    #
    cuni
    #
    wss
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    vz
    cB
    ctb
    cC
    @6
    @10
    vx
    @1
    cB
    @5
    @9
    vy
    @1
    cB
    @1
    cB
    wceq
    #
    @4
    @8
    @0
    @11
    @3
    @7
    @1
    cB
    @2
    ineq1
    unieqd
    sseq2d
    raleqbi1dv
    raleqbi1dv
    vz
    vx
    vy
    df-bases
    elab2g
end
