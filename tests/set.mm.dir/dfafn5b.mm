include "cv.mm"
include "cafv.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "cmpt.mm"
include "wceq.mm"
include "dfafn5a.mm"
include "eqid.mm"
include "fnmpt.mm"
include "fneq1.mm"
include "syl5ibrcom.mm"
include "impbid2.mm"

theorem dfafn5b
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
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
  assert |- ( A. x e. A ( F ''' x ) e. V -> ( F Fn A <-> F = ( x e. A |-> ( F ''' x ) ) ) )

  proof
    vx
    cv
    cF
    cafv
    #
    cV
    wcel
    vx
    cA
    wral
    #
    cF
    cA
    wfn
    #
    cF
    vx
    cA
    @0
    cmpt
    #
    wceq
    #
    vx
    cA
    cF
    dfafn5a
    @1
    @2
    @4
    @3
    cA
    wfn
    vx
    cA
    @0
    @3
    cV
    @3
    eqid
    fnmpt
    cA
    cF
    @3
    fneq1
    syl5ibrcom
    impbid2
end
