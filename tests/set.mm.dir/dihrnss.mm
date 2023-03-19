include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "clss.mm"
include "cfv.mm"
include "wss.mm"
include "eqid.mm"
include "dihrnlss.mm"
include "lssss.mm"
include "syl.mm"

theorem dihrnss
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume dihrnss.h: |- H = ( LHyp ` K )
  assume dihrnss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihrnss.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihrnss.v: |- V = ( Base ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> X C_ V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cI
    crn
    wcel
    wa
    cX
    cU
    clss
    cfv
    #
    wcel
    cX
    cV
    wss
    @0
    cU
    cH
    cI
    cK
    cW
    cX
    dihrnss.h
    dihrnss.u
    dihrnss.i
    @0
    eqid
    #
    dihrnlss
    @0
    cX
    cV
    cU
    dihrnss.v
    @1
    lssss
    syl
end
