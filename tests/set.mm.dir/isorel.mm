include "wiso.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "df-isom.mm"
include "simprbi.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem isorel
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( H Isom R , S ( A , B ) /\ ( C e. A /\ D e. A ) ) -> ( C R D <-> ( H ` C ) S ( H ` D ) ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
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
    @1
    cH
    cfv
    #
    @2
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
    cC
    cA
    wcel
    cD
    cA
    wcel
    wa
    cC
    cD
    cR
    wbr
    #
    cC
    cH
    cfv
    #
    cD
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    @0
    cA
    cB
    cH
    wf1o
    @8
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    simprbi
    @7
    @13
    cC
    @2
    cR
    wbr
    #
    @10
    @5
    cS
    wbr
    #
    wb
    vx
    vy
    cC
    cD
    cA
    cA
    @1
    cC
    wceq
    #
    @3
    @14
    @6
    @15
    @1
    cC
    @2
    cR
    breq1
    @16
    @4
    @10
    @5
    cS
    @1
    cC
    cH
    fveq2
    breq1d
    bibi12d
    @2
    cD
    wceq
    #
    @14
    @9
    @15
    @12
    @2
    cD
    cC
    cR
    breq2
    @17
    @5
    @11
    @10
    cS
    @2
    cD
    cH
    fveq2
    breq2d
    bibi12d
    rspc2v
    mpan9
end
