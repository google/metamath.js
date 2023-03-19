include "wcel.mm"
include "csb.mm"
include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "wceq.mm"
include "eleq2d.mm"
include "sbcie2g.mm"
include "abbi1dv.mm"
include "syl5eq.mm"

theorem csbie2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vz: setvar z
  assume csbie2g.1: |- ( x = y -> B = C )
  assume csbie2g.2: |- ( y = A -> C = D )

  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint D y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint D z
  disjoint V z
  assert |- ( A e. V -> [_ A / x ]_ B = D )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    csb
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vz
    cab
    cD
    vx
    vz
    cA
    cB
    df-csb
    @0
    @3
    vz
    cD
    @2
    @1
    cC
    wcel
    @1
    cD
    wcel
    vx
    vy
    cA
    cV
    vx
    cv
    vy
    cv
    #
    wceq
    cB
    cC
    @1
    csbie2g.1
    eleq2d
    @4
    cA
    wceq
    cC
    cD
    @1
    csbie2g.2
    eleq2d
    sbcie2g
    abbi1dv
    syl5eq
end
