include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "cfv.mm"
include "crn.mm"
include "cdia.mm"
include "wfn.mm"
include "eqid.mm"
include "dibfna.mm"
include "fnfun.mm"
include "syl.mm"
include "fvelrn.mm"
include "sylan.mm"

theorem dibclN
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dibcl.h: |- H = ( LHyp ` K )
  assume dibcl.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. dom I ) -> ( I ` X ) e. ran I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    wfun
    #
    cX
    cI
    cdm
    wcel
    cX
    cI
    cfv
    cI
    crn
    wcel
    @0
    cI
    cW
    cK
    cdia
    cfv
    cfv
    #
    cdm
    #
    wfn
    @1
    cH
    cI
    @2
    cK
    chlt
    cW
    dibcl.h
    @2
    eqid
    dibcl.i
    dibfna
    @3
    cI
    fnfun
    syl
    cX
    cI
    fvelrn
    sylan
end
