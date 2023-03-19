include "cfv.mm"
include "csn.mm"
include "cres.mm"
include "crn.mm"
include "wcel.mm"
include "cima.mm"
include "df-ima.mm"
include "eleq2i.mm"
include "cop.mm"
include "cv.mm"
include "wex.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "spcegv.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "elimasng.mm"
include "mpan2.mm"
include "elrn2g.mm"
include "mp1i.mm"
include "3imtr4d.mm"
include "syl5bir.mm"

theorem fvrnressn
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x


  assert |- ( X e. V -> ( ( F ` X ) e. ran ( F |` { X } ) -> ( F ` X ) e. ran F ) )

  proof
    cX
    cF
    cfv
    #
    cF
    cX
    csn
    #
    cres
    crn
    #
    wcel
    @0
    cF
    @1
    cima
    #
    wcel
    #
    cX
    cV
    wcel
    #
    @0
    cF
    crn
    wcel
    #
    @3
    @2
    @0
    cF
    @1
    df-ima
    eleq2i
    @5
    cX
    @0
    cop
    #
    cF
    wcel
    #
    vx
    cv
    #
    @0
    cop
    #
    cF
    wcel
    #
    vx
    wex
    #
    @4
    @6
    @11
    @8
    vx
    cX
    cV
    @9
    cX
    wceq
    @10
    @7
    cF
    @9
    cX
    @0
    opeq1
    eleq1d
    spcegv
    @5
    @0
    cvv
    wcel
    #
    @4
    @8
    wb
    cX
    cF
    fvex
    #
    cF
    cX
    @0
    cV
    cvv
    elimasng
    mpan2
    @13
    @6
    @12
    wb
    @5
    @14
    vx
    @0
    cF
    cvv
    elrn2g
    mp1i
    3imtr4d
    syl5bir
end
