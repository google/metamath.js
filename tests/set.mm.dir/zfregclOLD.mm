include "wel.mm"
include "wex.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wcel.mm"
include "wceq.mm"
include "eleq2.mm"
include "exbidv.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "nfre1.mm"
include "wal.mm"
include "wa.mm"
include "axreg2.mm"
include "df-ral.mm"
include "rexbii.mm"
include "df-rex.mm"
include "bitr2i.mm"
include "sylib.mm"
include "exlimi.mm"
include "vtocl.mm"

theorem zfregclOLD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume zfregclOLD.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( E. x x e. A -> E. x e. A A. y e. x -. y e. A )

  proof
    vx
    vz
    wel
    #
    vx
    wex
    #
    vy
    vz
    wel
    #
    wn
    #
    vy
    vx
    cv
    #
    wral
    #
    vx
    vz
    cv
    #
    wrex
    #
    wi
    @4
    cA
    wcel
    #
    vx
    wex
    #
    vy
    cv
    #
    cA
    wcel
    #
    wn
    #
    vy
    @4
    wral
    #
    vx
    cA
    wrex
    #
    wi
    vz
    cA
    zfregclOLD.1
    @6
    cA
    wceq
    #
    @1
    @9
    @7
    @14
    @15
    @0
    @8
    vx
    @6
    cA
    @4
    eleq2
    exbidv
    @5
    @13
    vx
    @6
    cA
    @15
    @3
    @12
    vy
    @4
    @15
    @2
    @11
    @6
    cA
    @10
    eleq2
    notbid
    ralbidv
    rexeqbi1dv
    imbi12d
    @0
    @7
    vx
    @5
    vx
    @6
    nfre1
    @0
    @0
    vy
    vx
    wel
    @3
    wi
    vy
    wal
    #
    wa
    vx
    wex
    #
    @7
    vx
    vz
    vy
    axreg2
    @7
    @16
    vx
    @6
    wrex
    @17
    @5
    @16
    vx
    @6
    @3
    vy
    @4
    df-ral
    rexbii
    @16
    vx
    @6
    df-rex
    bitr2i
    sylib
    exlimi
    vtocl
end
