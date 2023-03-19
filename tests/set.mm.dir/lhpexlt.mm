include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cp1.mm"
include "ccvr.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "simpl.mm"
include "eqid.mm"
include "lhpbase.mm"
include "adantl.mm"
include "lhp1cvr.mm"
include "1cvratex.mm"
include "syl3anc.mm"

theorem lhpexlt
  let cA: class A
  let c.lt: class .<
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  assume lhpatltex.s: |- .< = ( lt ` K )
  assume lhpatltex.a: |- A = ( Atoms ` K )
  assume lhpatltex.h: |- H = ( LHyp ` K )

  disjoint A p
  disjoint K p
  disjoint .< p
  disjoint W p
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A p .< W )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    @0
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    cK
    cp1
    cfv
    #
    cK
    ccvr
    cfv
    #
    wbr
    vp
    cv
    cW
    c.lt
    wbr
    vp
    cA
    wrex
    @0
    @1
    simpl
    @1
    @3
    @0
    @2
    cH
    cK
    cW
    @2
    eqid
    #
    lhpatltex.h
    lhpbase
    adantl
    chlt
    @5
    @4
    cH
    cK
    cW
    @4
    eqid
    #
    @5
    eqid
    #
    lhpatltex.h
    lhp1cvr
    cA
    @2
    @5
    c.lt
    @4
    cK
    cW
    vp
    @6
    lhpatltex.s
    @7
    @8
    lhpatltex.a
    1cvratex
    syl3anc
end
