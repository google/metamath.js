include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "cfv.mm"
include "crn.mm"
include "cdvh.mm"
include "clss.mm"
include "wf1.mm"
include "eqid.mm"
include "dihf11.mm"
include "adantr.mm"
include "f1fn.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "sylancom.mm"

theorem dihcl
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihfn.b: |- B = ( Base ` K )
  assume dihfn.h: |- H = ( LHyp ` K )
  assume dihfn.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B ) -> ( I ` X ) e. ran I )

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
    cB
    wcel
    #
    cI
    cB
    wfn
    #
    cX
    cI
    cfv
    cI
    crn
    wcel
    @0
    @1
    wa
    cB
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clss
    cfv
    #
    cI
    wf1
    #
    @2
    @0
    @5
    @1
    cB
    @4
    @3
    cH
    cI
    cK
    cW
    dihfn.b
    dihfn.h
    dihfn.i
    @3
    eqid
    @4
    eqid
    dihf11
    adantr
    cB
    @4
    cI
    f1fn
    syl
    cB
    cX
    cI
    fnfvelrn
    sylancom
end
