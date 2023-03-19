include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wbr.mm"
include "wrel.mm"
include "fnrel.mm"
include "dfrel4v.mm"
include "sylib.mm"
include "fnbr.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "eqcom.mm"
include "fnbrfvb.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "opabbidv.mm"
include "eqtrd.mm"
include "df-mpt.mm"
include "syl6eqr.mm"
include "fvex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem dffn5
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cB: class B
  let cY: class Y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F y
  disjoint Y x
  assert |- ( F Fn A <-> F = ( x e. A |-> ( F ` x ) ) )

  proof
    cF
    cA
    wfn
    #
    cF
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    wceq
    #
    @0
    cF
    @1
    cA
    wcel
    #
    vy
    cv
    #
    @2
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @3
    @0
    cF
    @1
    @6
    cF
    wbr
    #
    vx
    vy
    copab
    #
    @9
    @0
    cF
    wrel
    cF
    @11
    wceq
    cA
    cF
    fnrel
    vx
    vy
    cF
    dfrel4v
    sylib
    @0
    @10
    @8
    vx
    vy
    @0
    @10
    @5
    @10
    wa
    @8
    @0
    @10
    @5
    @0
    @10
    @5
    cA
    @1
    @6
    cF
    fnbr
    ex
    pm4.71rd
    @0
    @5
    @7
    @10
    @7
    @2
    @6
    wceq
    @0
    @5
    wa
    @10
    @6
    @2
    eqcom
    cA
    @1
    @6
    cF
    fnbrfvb
    syl5bb
    pm5.32da
    bitr4d
    opabbidv
    eqtrd
    vx
    vy
    cA
    @2
    df-mpt
    syl6eqr
    @4
    @0
    @3
    cA
    wfn
    vx
    cA
    @2
    @3
    @1
    cF
    fvex
    @3
    eqid
    fnmpti
    cA
    cF
    @3
    fneq1
    mpbiri
    impbii
end
