include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cdia.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "dibdiadm.mm"
include "eleq2d.mm"
include "diaeldm.mm"
include "bitrd.mm"

theorem dibeldmN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume dibfn.b: |- B = ( Base ` K )
  assume dibfn.l: |- .<_ = ( le ` K )
  assume dibfn.h: |- H = ( LHyp ` K )
  assume dibfn.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( K e. V /\ W e. H ) -> ( X e. dom I <-> ( X e. B /\ X .<_ W ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    cdm
    #
    wcel
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cdm
    #
    wcel
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    @0
    @1
    @3
    cX
    cH
    cI
    @2
    cK
    cV
    cW
    dibfn.h
    @2
    eqid
    #
    dibfn.i
    dibdiadm
    eleq2d
    cB
    cH
    @2
    cK
    c.le
    cV
    cW
    cX
    dibfn.b
    dibfn.l
    dibfn.h
    @4
    diaeldm
    bitrd
end
