include "wceq.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "breq12d.mm"
include "bibi2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "df-isom.mm"
include "3bitr4g.mm"

theorem isoeq1
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cT: class T


  assert |- ( H = G -> ( H Isom R , S ( A , B ) <-> G Isom R , S ( A , B ) ) )

  proof
    cH
    cG
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
    cA
    cB
    cG
    wf1o
    #
    @4
    @2
    cG
    cfv
    #
    @3
    cG
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
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    cR
    cS
    cG
    wiso
    @0
    @1
    @10
    @9
    @15
    cA
    cB
    cH
    cG
    f1oeq1
    @0
    @8
    @14
    vx
    vy
    cA
    cA
    @0
    @7
    @13
    @4
    @0
    @5
    @11
    @6
    @12
    cS
    @2
    cH
    cG
    fveq1
    @3
    cH
    cG
    fveq1
    breq12d
    bibi2d
    2ralbidv
    anbi12d
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
    cS
    cG
    df-isom
    3bitr4g
end
