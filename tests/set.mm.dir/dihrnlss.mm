include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dihsslss.mm"
include "sselda.mm"

theorem dihrnlss
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume dihsslss.h: |- H = ( LHyp ` K )
  assume dihsslss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihsslss.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihsslss.s: |- S = ( LSubSp ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> X e. S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cI
    crn
    cS
    cX
    cS
    cU
    cH
    cI
    cK
    cW
    dihsslss.h
    dihsslss.u
    dihsslss.i
    dihsslss.s
    dihsslss
    sselda
end
