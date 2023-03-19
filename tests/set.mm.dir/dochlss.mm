include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cdih.mm"
include "crn.mm"
include "eqid.mm"
include "dochcl.mm"
include "dihrnlss.mm"
include "syldan.mm"

theorem dochlss
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume dochlss.h: |- H = ( LHyp ` K )
  assume dochlss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochlss.v: |- V = ( Base ` U )
  assume dochlss.s: |- S = ( LSubSp ` U )
  assume dochlss.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V ) -> ( ._|_ ` X ) e. S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cV
    wss
    cX
    c.pe
    cfv
    #
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    @0
    cS
    wcel
    cU
    cH
    @1
    cK
    c.pe
    cV
    cW
    cX
    dochlss.h
    @1
    eqid
    #
    dochlss.u
    dochlss.v
    dochlss.o
    dochcl
    cS
    cU
    cH
    @1
    cK
    cW
    @0
    dochlss.h
    dochlss.u
    @2
    dochlss.s
    dihrnlss
    syldan
end
