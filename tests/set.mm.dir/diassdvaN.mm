include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cv.mm"
include "ctrl.mm"
include "cltrn.mm"
include "crab.mm"
include "eqid.mm"
include "diaval.mm"
include "ssrab2.mm"
include "wceq.mm"
include "dvavbase.mm"
include "adantr.mm"
include "syl5sseqr.mm"
include "eqsstrd.mm"

theorem diassdvaN
  let cB: class B
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume diassdva.b: |- B = ( Base ` K )
  assume diassdva.l: |- .<_ = ( le ` K )
  assume diassdva.h: |- H = ( LHyp ` K )
  assume diassdva.i: |- I = ( ( DIsoA ` K ) ` W )
  assume diassdva.u: |- U = ( ( DVecA ` K ) ` W )
  assume diassdva.v: |- V = ( Base ` U )


  assert |- ( ( ( K e. Y /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) C_ V )

  proof
    cK
    cY
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    wa
    #
    cX
    cI
    cfv
    vf
    cv
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    cX
    c.le
    wbr
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crab
    #
    cV
    cB
    @3
    @5
    vf
    cH
    cI
    cK
    c.le
    cY
    cW
    cX
    diassdva.b
    diassdva.l
    diassdva.h
    @5
    eqid
    #
    @3
    eqid
    diassdva.i
    diaval
    @2
    @5
    @6
    cV
    @4
    vf
    @5
    ssrab2
    @0
    cV
    @5
    wceq
    @1
    @5
    cU
    cH
    cK
    cV
    cW
    cY
    diassdva.h
    @7
    diassdva.u
    diassdva.v
    dvavbase
    adantr
    syl5sseqr
    eqsstrd
end
