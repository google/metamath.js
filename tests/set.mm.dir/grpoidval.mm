include "cgr.mm"
include "wcel.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "wa.mm"
include "gidval.mm"
include "wi.mm"
include "wrex.mm"
include "wreu.mm"
include "w3a.mm"
include "wb.mm"
include "simpl.mm"
include "ralimi.mm"
include "rgenw.mm"
include "a1i.mm"
include "grpoidinv.mm"
include "reximi.mm"
include "syl.mm"
include "grpoideu.mm"
include "3jca.mm"
include "reupick2.mm"
include "sylan.mm"
include "riotabidva.mm"
include "eqtr4d.mm"
include "syl5eq.mm"

theorem grpoidval
  let vx: setvar x
  let vu: setvar u
  let cU: class U
  let cG: class G
  let cX: class X
  let vy: setvar y
  let cA: class A
  assume grpoidval.1: |- X = ran G
  assume grpoidval.2: |- U = ( GId ` G )

  disjoint u x
  disjoint G u
  disjoint G x
  disjoint U u
  disjoint U x
  disjoint X u
  disjoint X x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint u y
  disjoint G y
  disjoint U y
  disjoint X y
  assert |- ( G e. GrpOp -> U = ( iota_ u e. X A. x e. X ( u G x ) = x ) )

  proof
    cG
    cgr
    wcel
    #
    cU
    cG
    cgi
    cfv
    #
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    @3
    wceq
    #
    vx
    cX
    wral
    #
    vu
    cX
    crio
    #
    grpoidval.2
    @0
    @1
    @4
    @3
    @2
    cG
    co
    @3
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    crio
    @6
    vx
    vu
    cG
    cgr
    cX
    grpoidval.1
    gidval
    @0
    @5
    @9
    vu
    cX
    @0
    @9
    @5
    wi
    #
    vu
    cX
    wral
    #
    @9
    vu
    cX
    wrex
    #
    @5
    vu
    cX
    wreu
    #
    w3a
    @2
    cX
    wcel
    @5
    @9
    wb
    @0
    @11
    @12
    @13
    @11
    @0
    @10
    vu
    cX
    @8
    @4
    vx
    cX
    @4
    @7
    simpl
    ralimi
    rgenw
    a1i
    @0
    @8
    vy
    cv
    #
    @3
    cG
    co
    @2
    wceq
    @3
    @14
    cG
    co
    @2
    wceq
    wa
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    @12
    vx
    vy
    vu
    cG
    cX
    grpoidval.1
    grpoidinv
    @17
    @9
    vu
    cX
    @16
    @8
    vx
    cX
    @8
    @15
    simpl
    ralimi
    reximi
    syl
    vx
    vu
    cG
    cX
    grpoidval.1
    grpoideu
    3jca
    @5
    @9
    vu
    cX
    reupick2
    sylan
    riotabidva
    eqtr4d
    syl5eq
end
