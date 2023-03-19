include "wceq.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "breq.mm"
include "bibi2d.mm"
include "2ralbidv.mm"
include "anbi2d.mm"
include "df-isom.mm"
include "3bitr4g.mm"

theorem isoeq3
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G


  assert |- ( S = T -> ( H Isom R , S ( A , B ) <-> H Isom R , T ( A , B ) ) )

  proof
    cS
    cT
    wceq
    #
    cA
    cB
    cH
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @2
    cH
    cfv
    #
    @3
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @1
    @4
    @5
    @6
    cT
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    cR
    cT
    cH
    wiso
    @0
    @9
    @12
    @1
    @0
    @8
    @11
    vx
    vy
    cA
    cA
    @0
    @7
    @10
    @4
    @5
    @6
    cS
    cT
    breq
    bibi2d
    2ralbidv
    anbi2d
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    vx
    vy
    cA
    cB
    cR
    cT
    cH
    df-isom
    3bitr4g
end
