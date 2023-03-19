include "wiso.mm"
include "cv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "wal.mm"
include "wa.mm"
include "wfr.mm"
include "wor.mm"
include "wwe.mm"
include "simpl.mm"
include "weq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "spv.mm"
include "adantl.mm"
include "isofrlem.mm"
include "wi.mm"
include "isosolem.mm"
include "adantr.mm"
include "anim12d.mm"
include "df-we.mm"
include "3imtr4g.mm"

theorem isowe2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint S x
  disjoint H x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint R y
  disjoint S y
  disjoint H y
  assert |- ( ( H Isom R , S ( A , B ) /\ A. x ( H " x ) e. _V ) -> ( S We B -> R We A ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cH
    vx
    cv
    #
    cima
    #
    cvv
    wcel
    #
    vx
    wal
    #
    wa
    #
    cB
    cS
    wfr
    #
    cB
    cS
    wor
    #
    wa
    cA
    cR
    wfr
    #
    cA
    cR
    wor
    #
    wa
    cB
    cS
    wwe
    cA
    cR
    wwe
    @5
    @6
    @8
    @7
    @9
    @5
    vy
    cA
    cB
    cR
    cS
    cH
    @0
    @4
    simpl
    @4
    cH
    vy
    cv
    #
    cima
    #
    cvv
    wcel
    #
    @0
    @3
    @12
    vx
    vy
    vx
    vy
    weq
    @2
    @11
    cvv
    @1
    @10
    cH
    imaeq2
    eleq1d
    spv
    adantl
    isofrlem
    @0
    @7
    @9
    wi
    @4
    cA
    cB
    cR
    cS
    cH
    isosolem
    adantr
    anim12d
    cB
    cS
    df-we
    cA
    cR
    df-we
    3imtr4g
end
