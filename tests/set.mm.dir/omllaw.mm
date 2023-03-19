include "coml.mm"
include "wcel.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "col.mm"
include "isoml.mm"
include "simprbi.mm"
include "breq1.mm"
include "id.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem omllaw
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume omllaw.b: |- B = ( Base ` K )
  assume omllaw.l: |- .<_ = ( le ` K )
  assume omllaw.j: |- .\/ = ( join ` K )
  assume omllaw.m: |- ./\ = ( meet ` K )
  assume omllaw.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X .<_ Y -> Y = ( X .\/ ( Y ./\ ( ._|_ ` X ) ) ) ) )

  proof
    cK
    coml
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    cY
    cX
    c.pe
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    wi
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    @10
    @9
    @10
    @9
    c.pe
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @2
    wa
    @8
    @0
    cK
    col
    wcel
    @17
    vx
    vy
    cB
    c.or
    cK
    c.le
    c.an
    c.pe
    omllaw.b
    omllaw.l
    omllaw.j
    omllaw.m
    omllaw.o
    isoml
    simprbi
    @16
    @8
    cX
    @10
    c.le
    wbr
    #
    @10
    cX
    @10
    @4
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    wi
    vx
    vy
    cX
    cY
    cB
    cB
    @9
    cX
    wceq
    #
    @11
    @18
    @15
    @21
    @9
    cX
    @10
    c.le
    breq1
    @22
    @14
    @20
    @10
    @22
    @9
    cX
    @13
    @19
    c.or
    @22
    id
    @22
    @12
    @4
    @10
    c.an
    @9
    cX
    c.pe
    fveq2
    oveq2d
    oveq12d
    eqeq2d
    imbi12d
    @10
    cY
    wceq
    #
    @18
    @3
    @21
    @7
    @10
    cY
    cX
    c.le
    breq2
    @23
    @10
    cY
    @20
    @6
    @23
    id
    @23
    @19
    @5
    cX
    c.or
    @10
    cY
    @4
    c.an
    oveq1
    oveq2d
    eqeq12d
    imbi12d
    rspc2v
    syl5com
    3impib
end
