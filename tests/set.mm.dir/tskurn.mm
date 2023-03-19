include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "wf.mm"
include "w3a.mm"
include "crn.mm"
include "cuni.mm"
include "simp1l.mm"
include "simp1r.mm"
include "wss.mm"
include "csdm.mm"
include "wbr.mm"
include "frn.mm"
include "3ad2ant3.mm"
include "cdom.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "tskwe2.mm"
include "syl.mm"
include "simp2.mm"
include "trss.mm"
include "sylc.mm"
include "ssnum.mm"
include "syl2anc.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fodomnum.mm"
include "tsksdom.mm"
include "domsdomtr.mm"
include "tskssel.mm"
include "syl3anc.mm"
include "tskuni.mm"

theorem tskurn
  let cA: class A
  let cT: class T
  let cF: class F


  assert |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ F : A --> T ) -> U. ran F e. T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    wa
    #
    cA
    cT
    wcel
    #
    cA
    cT
    cF
    wf
    #
    w3a
    #
    @0
    @1
    cF
    crn
    #
    cT
    wcel
    #
    @6
    cuni
    cT
    wcel
    @0
    @1
    @3
    @4
    simp1l
    #
    @0
    @1
    @3
    @4
    simp1r
    #
    @5
    @0
    @6
    cT
    wss
    #
    @6
    cT
    csdm
    wbr
    #
    @7
    @8
    @4
    @2
    @10
    @3
    cA
    cT
    cF
    frn
    3ad2ant3
    @5
    @6
    cA
    cdom
    wbr
    #
    cA
    cT
    csdm
    wbr
    #
    @11
    @5
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    @6
    cF
    wfo
    #
    @12
    @5
    cT
    @14
    wcel
    #
    cA
    cT
    wss
    #
    @15
    @5
    @0
    @17
    @8
    cT
    tskwe2
    syl
    @5
    @1
    @3
    @18
    @9
    @2
    @3
    @4
    simp2
    #
    cT
    cA
    trss
    sylc
    cT
    cA
    ssnum
    syl2anc
    @4
    @2
    @16
    @3
    @4
    cF
    cA
    wfn
    @16
    cA
    cT
    cF
    ffn
    cA
    cF
    dffn4
    sylib
    3ad2ant3
    cA
    @6
    cF
    fodomnum
    sylc
    @5
    @0
    @3
    @13
    @8
    @19
    cA
    cT
    tsksdom
    syl2anc
    @6
    cA
    cT
    domsdomtr
    syl2anc
    @6
    cT
    tskssel
    syl3anc
    @6
    cT
    tskuni
    syl3anc
end
