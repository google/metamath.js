include "csubgr.mm"
include "wbr.mm"
include "cumgr.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cuhgr.mm"
include "umgruhgr.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3.mm"
include "subgruhgredgd.mm"
include "ciedg.mm"
include "wfun.mm"
include "wss.mm"
include "eqid.mm"
include "uhgrfun.mm"
include "syl.mm"
include "cvtx.mm"
include "cedg.mm"
include "subgrprop2.mm"
include "simp2d.mm"
include "3ad2ant1.mm"
include "funssfv.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "simp2.mm"
include "wi.mm"
include "dmeqi.mm"
include "eleq2i.mm"
include "subgreldmiedg.mm"
include "ex.mm"
include "syl5bi.mm"
include "a1d.mm"
include "3imp.mm"
include "umgredg2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "prprrab.mm"
include "syl6eleq.mm"

theorem subumgredg2
  let cS: class S
  let ve: setvar e
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  assume subumgredg2.v: |- V = ( Vtx ` S )
  assume subumgredg2.i: |- I = ( iEdg ` S )

  disjoint I e
  disjoint V e
  disjoint X e
  assert |- ( ( S SubGraph G /\ G e. UMGraph /\ X e. dom I ) -> ( I ` X ) e. { e e. ~P V | ( # ` e ) = 2 } )

  proof
    cS
    cG
    csubgr
    wbr
    #
    cG
    cumgr
    wcel
    #
    cX
    cI
    cdm
    #
    wcel
    #
    w3a
    #
    cX
    cI
    cfv
    #
    ve
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    ve
    cV
    cpw
    #
    c0
    csn
    cdif
    #
    crab
    #
    @8
    ve
    @9
    crab
    @4
    @5
    @10
    wcel
    @5
    chash
    cfv
    #
    c2
    wceq
    #
    @5
    @11
    wcel
    @4
    cS
    cG
    cI
    cV
    cX
    subumgredg2.v
    subumgredg2.i
    @1
    @0
    cG
    cuhgr
    wcel
    #
    @3
    cG
    umgruhgr
    #
    3ad2ant2
    @0
    @1
    @3
    simp1
    @0
    @1
    @3
    simp3
    #
    subgruhgredgd
    @4
    @12
    cX
    cG
    ciedg
    cfv
    #
    cfv
    #
    chash
    cfv
    #
    c2
    @4
    @5
    @18
    chash
    @4
    @17
    wfun
    #
    cI
    @17
    wss
    #
    @3
    @5
    @18
    wceq
    @1
    @0
    @20
    @3
    @1
    @14
    @20
    @15
    @17
    cG
    @17
    eqid
    #
    uhgrfun
    syl
    3ad2ant2
    @0
    @1
    @21
    @3
    @0
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wss
    @21
    cS
    cedg
    cfv
    #
    @23
    cpw
    wss
    @24
    @17
    cS
    @25
    cG
    cI
    @23
    @23
    eqid
    @24
    eqid
    #
    subumgredg2.i
    @22
    @25
    eqid
    subgrprop2
    simp2d
    3ad2ant1
    @16
    @20
    @21
    @3
    w3a
    @18
    @5
    cX
    @17
    cI
    funssfv
    eqcomd
    syl3anc
    fveq2d
    @4
    @1
    cX
    @17
    cdm
    wcel
    #
    @19
    c2
    wceq
    @0
    @1
    @3
    simp2
    @0
    @1
    @3
    @27
    @0
    @3
    @27
    wi
    @1
    @3
    cX
    cS
    ciedg
    cfv
    #
    cdm
    #
    wcel
    #
    @0
    @27
    @2
    @29
    cX
    cI
    @28
    subumgredg2.i
    dmeqi
    eleq2i
    @0
    @30
    @27
    cS
    cG
    cX
    subgreldmiedg
    ex
    syl5bi
    a1d
    3imp
    @17
    cG
    @24
    cX
    @26
    @22
    umgredg2
    syl2anc
    eqtrd
    @8
    @13
    ve
    @5
    @10
    @6
    @5
    wceq
    @7
    @12
    c2
    @6
    @5
    chash
    fveq2
    eqeq1d
    elrab
    sylanbrc
    ve
    cV
    prprrab
    syl6eleq
end
