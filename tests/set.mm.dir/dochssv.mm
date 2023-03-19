include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cdih.mm"
include "crn.mm"
include "eqid.mm"
include "dochcl.mm"
include "dihrnss.mm"
include "syldan.mm"

theorem dochssv
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume dochssv.h: |- H = ( LHyp ` K )
  assume dochssv.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochssv.v: |- V = ( Base ` U )
  assume dochssv.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V ) -> ( ._|_ ` X ) C_ V )

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
    cV
    wss
    cU
    cH
    @1
    cK
    c.pe
    cV
    cW
    cX
    dochssv.h
    @1
    eqid
    #
    dochssv.u
    dochssv.v
    dochssv.o
    dochcl
    cU
    cH
    @1
    cK
    cV
    cW
    @0
    dochssv.h
    dochssv.u
    @2
    dochssv.v
    dihrnss
    syldan
end
