include "crg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wss.mm"
include "subrgss.mm"
include "selpw.mm"
include "sylibr.mm"
include "a1i.mm"
include "ssrdv.mm"
include "subrgid.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "subrgint.mm"
include "3adant1.mm"
include "ismred.mm"

theorem subrgmre
  let cB: class B
  let cR: class R
  let va: setvar a
  assume subrgmre.b: |- B = ( Base ` R )


  assert |- ( R e. Ring -> ( SubRing ` R ) e. ( Moore ` B ) )

  proof
    cR
    crg
    wcel
    #
    cR
    csubrg
    cfv
    #
    cB
    va
    @0
    va
    @1
    cB
    cpw
    #
    va
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    wi
    @0
    @4
    @3
    cB
    wss
    @5
    @3
    cB
    cR
    subrgmre.b
    subrgss
    va
    cB
    selpw
    sylibr
    a1i
    ssrdv
    cB
    cR
    subrgmre.b
    subrgid
    @3
    @1
    wss
    @3
    c0
    wne
    @3
    cint
    @1
    wcel
    @0
    cR
    @3
    subrgint
    3adant1
    ismred
end
