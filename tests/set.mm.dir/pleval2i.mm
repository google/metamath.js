include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wne.mm"
include "cbs.mm"
include "cdm.mm"
include "wb.mm"
include "cfv.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "adantr.mm"
include "pltval.mm"
include "3expb.mm"
include "mpancom.mm"
include "biimpar.mm"
include "expr.mm"
include "necon1bd.mm"
include "orrd.mm"
include "ex.mm"

theorem pleval2i
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume pleval2.b: |- B = ( Base ` K )
  assume pleval2.l: |- .<_ = ( le ` K )
  assume pleval2.s: |- .< = ( lt ` K )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .<_ Y -> ( X .< Y \/ X = Y ) ) )

  proof
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    wceq
    #
    wo
    @2
    @3
    wa
    #
    @4
    @5
    @6
    @4
    cX
    cY
    @2
    @3
    cX
    cY
    wne
    #
    @4
    @2
    @4
    @3
    @7
    wa
    #
    cK
    cbs
    cdm
    #
    wcel
    #
    @2
    @4
    @8
    wb
    #
    @0
    @10
    @1
    @10
    cX
    cK
    cbs
    cfv
    cB
    cX
    cK
    cbs
    elfvdm
    pleval2.b
    eleq2s
    adantr
    @10
    @0
    @1
    @11
    @9
    cB
    cB
    c.lt
    cK
    c.le
    cX
    cY
    pleval2.l
    pleval2.s
    pltval
    3expb
    mpancom
    biimpar
    expr
    necon1bd
    orrd
    ex
end
