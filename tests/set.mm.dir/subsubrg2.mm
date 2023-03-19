include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "cin.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "subsubrg.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "eqrdv.mm"

theorem subsubrg2
  let cA: class A
  let cR: class R
  let cS: class S
  let va: setvar a
  assume subsubrg.s: |- S = ( R |`s A )


  assert |- ( A e. ( SubRing ` R ) -> ( SubRing ` S ) = ( ( SubRing ` R ) i^i ~P A ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    va
    cS
    csubrg
    cfv
    #
    @0
    cA
    cpw
    #
    cin
    #
    @1
    va
    cv
    #
    @2
    wcel
    @5
    @0
    wcel
    #
    @5
    cA
    wss
    #
    wa
    #
    @5
    @4
    wcel
    #
    cA
    @5
    cR
    cS
    subsubrg.s
    subsubrg
    @9
    @6
    @5
    @3
    wcel
    #
    wa
    @8
    @5
    @0
    @3
    elin
    @10
    @7
    @6
    va
    cA
    selpw
    anbi2i
    bitr2i
    syl6bb
    eqrdv
end
