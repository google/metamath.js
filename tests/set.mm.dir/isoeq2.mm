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
include "bibi1d.mm"
include "2ralbidv.mm"
include "anbi2d.mm"
include "df-isom.mm"
include "3bitr4g.mm"

theorem isoeq2
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


  assert |- ( R = T -> ( H Isom R , S ( A , B ) <-> H Isom T , S ( A , B ) ) )

  proof
    cR
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
    @3
    cH
    cfv
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
    @2
    @3
    cT
    wbr
    #
    @5
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
    cT
    cS
    cH
    wiso
    @0
    @7
    @10
    @1
    @0
    @6
    @9
    vx
    vy
    cA
    cA
    @0
    @4
    @8
    @5
    @2
    @3
    cR
    cT
    breq
    bibi1d
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
    cT
    cS
    cH
    df-isom
    3bitr4g
end
