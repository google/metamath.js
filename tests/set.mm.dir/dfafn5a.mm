include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "cafv.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "wbr.mm"
include "wrel.mm"
include "fnrel.mm"
include "dfrel4v.mm"
include "sylib.mm"
include "fnbr.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "eqcom.mm"
include "fnbrafvb.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "opabbidv.mm"
include "eqtrd.mm"
include "df-mpt.mm"
include "syl6eqr.mm"

theorem dfafn5a
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cB: class B
  let vk: setvar k

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F y
  disjoint k x
  assert |- ( F Fn A -> F = ( x e. A |-> ( F ''' x ) ) )

  proof
    cF
    cA
    wfn
    #
    cF
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @1
    cF
    cafv
    #
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    @4
    cmpt
    @0
    cF
    @1
    @3
    cF
    wbr
    #
    vx
    vy
    copab
    #
    @7
    @0
    cF
    wrel
    cF
    @9
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
    @8
    @6
    vx
    vy
    @0
    @8
    @2
    @8
    wa
    @6
    @0
    @8
    @2
    @0
    @8
    @2
    cA
    @1
    @3
    cF
    fnbr
    ex
    pm4.71rd
    @0
    @2
    @5
    @8
    @5
    @4
    @3
    wceq
    @0
    @2
    wa
    @8
    @3
    @4
    eqcom
    cA
    @1
    @3
    cF
    fnbrafvb
    syl5bb
    pm5.32da
    bitr4d
    opabbidv
    eqtrd
    vx
    vy
    cA
    @4
    df-mpt
    syl6eqr
end
