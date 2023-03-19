include "cfne.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "fnerel.mm"
include "brrelex2i.mm"
include "cuni.mm"
include "simpl.mm"
include "3eqtr3g.mm"
include "fvex.mm"
include "ssex.mm"
include "adantl.mm"
include "uniexb.mm"
include "sylib.mm"
include "eqeltrrd.mm"
include "sylibr.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "isfne.mm"
include "dfss3.mm"
include "eltg.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "bitr4d.mm"
include "pm5.21nii.mm"

theorem isfne4
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume isfne.1: |- X = U. A
  assume isfne.2: |- Y = U. B


  assert |- ( A Fne B <-> ( X = Y /\ A C_ ( topGen ` B ) ) )

  proof
    cA
    cB
    cfne
    wbr
    #
    cB
    cvv
    wcel
    #
    cX
    cY
    wceq
    #
    cA
    cB
    ctg
    cfv
    #
    wss
    #
    wa
    #
    cA
    cB
    cfne
    fnerel
    brrelex2i
    @5
    cB
    cuni
    #
    cvv
    wcel
    @1
    @5
    cA
    cuni
    #
    @6
    cvv
    @5
    cX
    cY
    @7
    @6
    @2
    @4
    simpl
    isfne.1
    isfne.2
    3eqtr3g
    @5
    cA
    cvv
    wcel
    #
    @7
    cvv
    wcel
    @4
    @8
    @2
    cA
    @3
    cB
    ctg
    fvex
    ssex
    adantl
    cA
    uniexb
    sylib
    eqeltrrd
    cB
    uniexb
    sylibr
    @1
    @0
    @2
    vx
    cv
    #
    cB
    @9
    cpw
    cin
    cuni
    wss
    #
    vx
    cA
    wral
    #
    wa
    @5
    vx
    cA
    cB
    cvv
    cX
    cY
    isfne.1
    isfne.2
    isfne
    @1
    @4
    @11
    @2
    @4
    @9
    @3
    wcel
    #
    vx
    cA
    wral
    @1
    @11
    vx
    cA
    @3
    dfss3
    @1
    @12
    @10
    vx
    cA
    @9
    cB
    cvv
    eltg
    ralbidv
    syl5bb
    anbi2d
    bitr4d
    pm5.21nii
end
