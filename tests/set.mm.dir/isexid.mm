include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "cexid.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "syl6eqr.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "df-exid.mm"
include "elab2g.mm"

theorem isexid
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cG: class G
  let cX: class X
  let vg: setvar g
  assume isexid.1: |- X = dom dom G

  disjoint G x
  disjoint G y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint G g
  disjoint g x
  disjoint g y
  disjoint X g
  assert |- ( G e. A -> ( G e. ExId <-> E. x e. X A. y e. X ( ( x G y ) = y /\ ( y G x ) = y ) ) )

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
    wceq
    #
    @1
    @0
    @2
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    @2
    cdm
    #
    cdm
    #
    wral
    #
    vx
    @9
    wrex
    @0
    @1
    cG
    co
    #
    @1
    wceq
    #
    @1
    @0
    cG
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    vg
    cG
    cexid
    cA
    @2
    cG
    wceq
    #
    @10
    @16
    vx
    @9
    cX
    @17
    @9
    cG
    cdm
    #
    cdm
    cX
    @17
    @8
    @18
    @2
    cG
    dmeq
    dmeqd
    isexid.1
    syl6eqr
    #
    @17
    @7
    @15
    vy
    @9
    cX
    @19
    @17
    @4
    @12
    @6
    @14
    @17
    @3
    @11
    @1
    @0
    @1
    @2
    cG
    oveq
    eqeq1d
    @17
    @5
    @13
    @1
    @1
    @0
    @2
    cG
    oveq
    eqeq1d
    anbi12d
    raleqbidv
    rexeqbidv
    vx
    vy
    vg
    df-exid
    elab2g
end
