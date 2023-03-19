include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "diaeldm.mm"
include "simplbda.mm"

theorem diadmleN
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  assume diadmle.l: |- .<_ = ( le ` K )
  assume diadmle.h: |- H = ( LHyp ` K )
  assume diadmle.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ X e. dom I ) -> X .<_ W )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cX
    cI
    cdm
    wcel
    cX
    cK
    cbs
    cfv
    #
    wcel
    cX
    cW
    c.le
    wbr
    @0
    cH
    cI
    cK
    c.le
    cV
    cW
    cX
    @0
    eqid
    diadmle.l
    diadmle.h
    diadmle.i
    diaeldm
    simplbda
end
