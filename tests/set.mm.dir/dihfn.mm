include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdvh.mm"
include "cfv.mm"
include "clss.mm"
include "wf1.mm"
include "wfn.mm"
include "eqid.mm"
include "dihf11.mm"
include "f1fn.mm"
include "syl.mm"

theorem dihfn
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume dihfn.b: |- B = ( Base ` K )
  assume dihfn.h: |- H = ( LHyp ` K )
  assume dihfn.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> I Fn B )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cI
    cB
    wfn
    cB
    @1
    @0
    cH
    cI
    cK
    cW
    dihfn.b
    dihfn.h
    dihfn.i
    @0
    eqid
    @1
    eqid
    dihf11
    cB
    @1
    cI
    f1fn
    syl
end
