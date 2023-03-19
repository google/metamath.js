include "wceq.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "f1oeq2.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "df-isom.mm"
include "3bitr4g.mm"

theorem isoeq4
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


  assert |- ( A = C -> ( H Isom R , S ( A , B ) <-> H Isom R , S ( C , B ) ) )

  proof
    cA
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
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    cC
    cB
    cH
    wf1o
    #
    @4
    vy
    cC
    wral
    #
    vx
    cC
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cC
    cB
    cR
    cS
    cH
    wiso
    @0
    @1
    @7
    @6
    @9
    cA
    cC
    cB
    cH
    f1oeq2
    @5
    @8
    vx
    cA
    cC
    @4
    vy
    cA
    cC
    raleq
    raleqbi1dv
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
    cC
    cB
    cR
    cS
    cH
    df-isom
    3bitr4g
end
