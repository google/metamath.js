include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "cgr.mm"
include "cablo.mm"
include "wb.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "oveq.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "bitrd.mm"
include "df-ablo.mm"
include "elrab2.mm"

theorem isablo
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cX: class X
  let vg: setvar g
  assume isabl.1: |- X = ran G

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint X g
  assert |- ( G e. AbelOp <-> ( G e. GrpOp /\ A. x e. X A. y e. X ( x G y ) = ( y G x ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vg
    cv
    #
    co
    #
    @1
    @0
    @2
    co
    #
    wceq
    #
    vy
    @2
    crn
    #
    wral
    #
    vx
    @6
    wral
    #
    @0
    @1
    cG
    co
    #
    @1
    @0
    cG
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vg
    cG
    cgr
    cablo
    @2
    cG
    wceq
    #
    @8
    @5
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @12
    @13
    @6
    cX
    wceq
    @8
    @15
    wb
    @13
    @6
    cG
    crn
    cX
    @2
    cG
    rneq
    isabl.1
    syl6eqr
    @7
    @14
    vx
    @6
    cX
    @5
    vy
    @6
    cX
    raleq
    raleqbi1dv
    syl
    @13
    @5
    @11
    vx
    vy
    cX
    cX
    @13
    @3
    @9
    @4
    @10
    @0
    @1
    @2
    cG
    oveq
    @1
    @0
    @2
    cG
    oveq
    eqeq12d
    2ralbidv
    bitrd
    vx
    vy
    vg
    df-ablo
    elrab2
end
