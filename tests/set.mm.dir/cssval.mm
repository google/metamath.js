include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "elex.mm"
include "ccss.mm"
include "cocv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "fveq12d.mm"
include "eqeq2d.mm"
include "abbidv.mm"
include "df-css.mm"
include "cbs.mm"
include "cpw.mm"
include "fvex.mm"
include "pwex.mm"
include "id.mm"
include "wss.mm"
include "eqid.mm"
include "ocvss.mm"
include "elpw.mm"
include "mpbir.mm"
include "syl6eqel.mm"
include "abssi.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem cssval
  let cC: class C
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  let cS: class S
  assume cssval.o: |- ._|_ = ( ocv ` W )
  assume cssval.c: |- C = ( CSubSp ` W )

  disjoint ._|_ s
  disjoint W s
  disjoint s w
  disjoint ._|_ w
  disjoint S s
  disjoint W w
  assert |- ( W e. X -> C = { s | s = ( ._|_ ` ( ._|_ ` s ) ) } )

  proof
    cW
    cX
    wcel
    cW
    cvv
    wcel
    #
    cC
    vs
    cv
    #
    @1
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    wceq
    #
    vs
    cab
    #
    wceq
    cW
    cX
    elex
    @0
    cC
    cW
    ccss
    cfv
    @5
    cssval.c
    vw
    cW
    @1
    @1
    vw
    cv
    #
    cocv
    cfv
    #
    cfv
    #
    @7
    cfv
    #
    wceq
    #
    vs
    cab
    @5
    cvv
    ccss
    @6
    cW
    wceq
    #
    @10
    @4
    vs
    @11
    @9
    @3
    @1
    @11
    @8
    @2
    @7
    c.pe
    @11
    @7
    cW
    cocv
    cfv
    c.pe
    @6
    cW
    cocv
    fveq2
    cssval.o
    syl6eqr
    #
    @11
    @1
    @7
    c.pe
    @12
    fveq1d
    fveq12d
    eqeq2d
    abbidv
    vw
    vs
    df-css
    @5
    cW
    cbs
    cfv
    #
    cpw
    #
    @13
    cW
    cbs
    fvex
    pwex
    @4
    vs
    @14
    @4
    @1
    @3
    @14
    @4
    id
    @3
    @14
    wcel
    @3
    @13
    wss
    @2
    c.pe
    @13
    cW
    @13
    eqid
    cssval.o
    ocvss
    @3
    @13
    @2
    c.pe
    fvex
    elpw
    mpbir
    syl6eqel
    abssi
    ssexi
    fvmpt
    syl5eq
    syl
end
