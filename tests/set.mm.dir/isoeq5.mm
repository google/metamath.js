include "wceq.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "f1oeq3.mm"
include "anbi1d.mm"
include "df-isom.mm"
include "3bitr4g.mm"

theorem isoeq5
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cT: class T


  assert |- ( B = C -> ( H Isom R , S ( A , B ) <-> H Isom R , S ( A , C ) ) )

  proof
    cB
    cC
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
    @2
    cH
    cfv
    @3
    cH
    cfv
    cS
    wbr
    wb
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cC
    cH
    wf1o
    #
    @4
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cC
    cR
    cS
    cH
    wiso
    @0
    @1
    @5
    @4
    cB
    cC
    cA
    cH
    f1oeq3
    anbi1d
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
    cC
    cR
    cS
    cH
    df-isom
    3bitr4g
end
