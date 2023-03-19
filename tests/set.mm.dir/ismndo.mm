include "cmndo.mm"
include "wcel.mm"
include "csem.mm"
include "cexid.mm"
include "cin.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "df-mndo.mm"
include "eleq2i.mm"
include "elin.mm"
include "isexid.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem ismndo
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cG: class G
  let cX: class X
  assume ismndo.1: |- X = dom dom G

  disjoint G x
  disjoint G y
  disjoint x y
  disjoint X x
  disjoint X y
  assert |- ( G e. A -> ( G e. MndOp <-> ( G e. SemiGrp /\ E. x e. X A. y e. X ( ( x G y ) = y /\ ( y G x ) = y ) ) ) )

  proof
    cG
    cmndo
    wcel
    cG
    csem
    cexid
    cin
    #
    wcel
    #
    cG
    cA
    wcel
    #
    cG
    csem
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    @5
    wceq
    @5
    @4
    cG
    co
    @5
    wceq
    wa
    vy
    cX
    wral
    vx
    cX
    wrex
    #
    wa
    #
    cmndo
    @0
    cG
    df-mndo
    eleq2i
    @1
    @3
    cG
    cexid
    wcel
    #
    wa
    @2
    @7
    cG
    csem
    cexid
    elin
    @2
    @8
    @6
    @3
    vx
    vy
    cA
    cG
    cX
    ismndo.1
    isexid
    anbi2d
    syl5bb
    syl5bb
end
