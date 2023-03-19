include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wf1o.mm"
include "islaut.mm"
include "simplbda.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem lautle
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume lautset.b: |- B = ( Base ` K )
  assume lautset.l: |- .<_ = ( le ` K )
  assume lautset.i: |- I = ( LAut ` K )


  assert |- ( ( ( K e. V /\ F e. I ) /\ ( X e. B /\ Y e. B ) ) -> ( X .<_ Y <-> ( F ` X ) .<_ ( F ` Y ) ) )

  proof
    cK
    cV
    wcel
    #
    cF
    cI
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    @2
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    c.le
    wbr
    #
    wb
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    cX
    cY
    c.le
    wbr
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.le
    wbr
    #
    wb
    #
    @0
    @1
    cB
    cB
    cF
    wf1o
    @9
    vx
    vy
    cV
    cB
    cF
    cI
    cK
    c.le
    lautset.b
    lautset.l
    lautset.i
    islaut
    simplbda
    @8
    @14
    cX
    @3
    c.le
    wbr
    #
    @11
    @6
    c.le
    wbr
    #
    wb
    vx
    vy
    cX
    cY
    cB
    cB
    @2
    cX
    wceq
    #
    @4
    @15
    @7
    @16
    @2
    cX
    @3
    c.le
    breq1
    @17
    @5
    @11
    @6
    c.le
    @2
    cX
    cF
    fveq2
    breq1d
    bibi12d
    @3
    cY
    wceq
    #
    @15
    @10
    @16
    @13
    @3
    cY
    cX
    c.le
    breq2
    @18
    @6
    @12
    @11
    c.le
    @3
    cY
    cF
    fveq2
    breq2d
    bibi12d
    rspc2v
    mpan9
end
