include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "diaeldm.mm"
include "simprbda.mm"

theorem diadmclN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume diadmcl.b: |- B = ( Base ` K )
  assume diadmcl.h: |- H = ( LHyp ` K )
  assume diadmcl.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ X e. dom I ) -> X e. B )

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
    cB
    wcel
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    cB
    cH
    cI
    cK
    @0
    cV
    cW
    cX
    diadmcl.b
    @0
    eqid
    diadmcl.h
    diadmcl.i
    diaeldm
    simprbda
end
