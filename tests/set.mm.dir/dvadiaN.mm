include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "simprr.mm"
include "cltrn.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "lssss.mm"
include "ad2antrl.mm"
include "dvavbase.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "docaclN.mm"
include "syldan.mm"
include "diaelrnN.mm"
include "eqeltrrd.mm"

theorem dvadiaN
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume dvadia.h: |- H = ( LHyp ` K )
  assume dvadia.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvadia.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dvadia.n: |- ._|_ = ( ( ocA ` K ) ` W )
  assume dvadia.s: |- S = ( LSubSp ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. S /\ ( ._|_ ` ( ._|_ ` X ) ) = X ) ) -> X e. ran I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cS
    wcel
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wceq
    #
    wa
    #
    wa
    #
    @3
    cX
    cI
    crn
    #
    @0
    @1
    @4
    simprr
    @0
    @5
    @2
    cW
    cK
    cltrn
    cfv
    cfv
    #
    wss
    #
    @3
    @7
    wcel
    @0
    @5
    @2
    @7
    wcel
    #
    @9
    @0
    @5
    cX
    @8
    wss
    @10
    @6
    cX
    cU
    cbs
    cfv
    #
    @8
    @1
    cX
    @11
    wss
    @0
    @4
    cS
    cX
    @11
    cU
    @11
    eqid
    #
    dvadia.s
    lssss
    ad2antrl
    @0
    @11
    @8
    wceq
    @5
    @8
    cU
    cH
    cK
    @11
    cW
    chlt
    dvadia.h
    @8
    eqid
    #
    dvadia.u
    @12
    dvavbase
    adantr
    sseqtrd
    @8
    cH
    cI
    cK
    c.pe
    cW
    cX
    dvadia.h
    @13
    dvadia.i
    dvadia.n
    docaclN
    syldan
    @2
    @8
    cH
    cI
    cK
    chlt
    cW
    dvadia.h
    @13
    dvadia.i
    diaelrnN
    syldan
    @8
    cH
    cI
    cK
    c.pe
    cW
    @2
    dvadia.h
    @13
    dvadia.i
    dvadia.n
    docaclN
    syldan
    eqeltrrd
end
