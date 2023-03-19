include "wrefrel.mm"
include "wsymrel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "cdm.mm"
include "wal.mm"
include "wrel.mm"
include "w3a.mm"
include "dfrefrel3.mm"
include "dfsymrel3.mm"
include "anbi12i.mm"
include "anandi3r.mm"
include "3anan32.mm"
include "3bitr2i.mm"
include "symrefref3.mm"
include "pm5.32ri.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem refsymrel3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( ( RefRel R /\ SymRel R ) <-> ( ( A. x e. dom R x R x /\ A. x A. y ( x R y -> y R x ) ) /\ Rel R ) )

  proof
    cR
    wrefrel
    #
    cR
    wsymrel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @3
    @4
    cR
    wbr
    #
    wi
    vy
    cR
    crn
    wral
    vx
    cR
    cdm
    #
    wral
    #
    @5
    @4
    @3
    cR
    wbr
    wi
    vy
    wal
    vx
    wal
    #
    wa
    #
    cR
    wrel
    #
    wa
    #
    @3
    @3
    cR
    wbr
    vx
    @6
    wral
    #
    @8
    wa
    #
    @10
    wa
    @2
    @7
    @10
    wa
    #
    @8
    @10
    wa
    #
    wa
    @7
    @10
    @8
    w3a
    @11
    @0
    @14
    @1
    @15
    vx
    vy
    cR
    dfrefrel3
    vx
    vy
    cR
    dfsymrel3
    anbi12i
    @7
    @10
    @8
    anandi3r
    @7
    @10
    @8
    3anan32
    3bitr2i
    @9
    @13
    @10
    @8
    @7
    @12
    vx
    vy
    cR
    symrefref3
    pm5.32ri
    anbi1i
    bitri
end
