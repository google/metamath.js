include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "ctrl.mm"
include "cfv.mm"
include "wrex.mm"
include "eqid.mm"
include "cdlemftr1.mm"
include "simpl.mm"
include "reximi.mm"
include "syl.mm"

theorem cdlemftr0
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cW: class W
  assume cdlemftr0.b: |- B = ( Base ` K )
  assume cdlemftr0.h: |- H = ( LHyp ` K )
  assume cdlemftr0.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint H f
  disjoint K f
  disjoint T f
  disjoint W f
  assert |- ( ( K e. HL /\ W e. H ) -> E. f e. T f =/= ( _I |` B ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    vf
    cv
    #
    cid
    cB
    cres
    wne
    #
    @0
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    cid
    wne
    #
    wa
    #
    vf
    cT
    wrex
    @1
    vf
    cT
    wrex
    cB
    @2
    cT
    vf
    cH
    cK
    cW
    cid
    cdlemftr0.b
    cdlemftr0.h
    cdlemftr0.t
    @2
    eqid
    cdlemftr1
    @4
    @1
    vf
    cT
    @1
    @3
    simpl
    reximi
    syl
end
