include "cvv.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "wceq.mm"
include "f1eq2.mm"
include "exbidv.mm"
include "f1eq3.mm"
include "df-dom.mm"
include "brabg.mm"
include "ex.mm"
include "wn.mm"
include "reldom.mm"
include "brrelexi.mm"
include "wf.mm"
include "f1f.mm"
include "cdm.mm"
include "fdm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "syl.mm"
include "exlimiv.mm"
include "pm5.21ni.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem brdomg
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y

  disjoint A f
  disjoint B f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  assert |- ( B e. C -> ( A ~<_ B <-> E. f f : A -1-1-> B ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    cC
    wcel
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    wb
    #
    wi
    @0
    @1
    @6
    vx
    cv
    #
    vy
    cv
    #
    @3
    wf1
    #
    vf
    wex
    cA
    @8
    @3
    wf1
    #
    vf
    wex
    @5
    vx
    vy
    cA
    cB
    cvv
    cC
    cdom
    @7
    cA
    wceq
    @9
    @10
    vf
    @7
    cA
    @8
    @3
    f1eq2
    exbidv
    @8
    cB
    wceq
    @10
    @4
    vf
    @8
    cB
    cA
    @3
    f1eq3
    exbidv
    vx
    vy
    vf
    df-dom
    brabg
    ex
    @0
    wn
    @6
    @1
    @2
    @0
    @5
    cA
    cB
    cdom
    reldom
    brrelexi
    @4
    @0
    vf
    @4
    cA
    cB
    @3
    wf
    #
    @0
    cA
    cB
    @3
    f1f
    @11
    cA
    @3
    cdm
    cvv
    cA
    cB
    @3
    fdm
    @3
    vf
    vex
    dmex
    syl6eqelr
    syl
    exlimiv
    pm5.21ni
    a1d
    pm2.61i
end
