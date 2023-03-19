include "cdprd.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cgsu.mm"
include "wrex.mm"
include "cop.mm"
include "cfv.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "eleq2s.mm"
include "df-br.mm"
include "sylibr.mm"
include "pm4.71ri.mm"
include "wb.mm"
include "cmpt.mm"
include "crn.mm"
include "dprdval.mm"
include "eleq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "syl6bb.mm"
include "ancoms.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem eldprd
  let cA: class A
  let cS: class S
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  assume dprdval.0: |- .0. = ( 0g ` G )
  assume dprdval.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }

  disjoint f h
  disjoint f i
  disjoint h i
  disjoint A f
  disjoint I f
  disjoint I h
  disjoint I i
  disjoint S f
  disjoint S h
  disjoint S i
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint g h
  disjoint g i
  disjoint g s
  disjoint g y
  disjoint h s
  disjoint h y
  disjoint i s
  disjoint i y
  disjoint s y
  disjoint .0. g
  disjoint I s
  disjoint S s
  disjoint G g
  disjoint G s
  disjoint W s
  assert |- ( dom S = I -> ( A e. ( G DProd S ) <-> ( G dom DProd S /\ E. f e. W A = ( G gsum f ) ) ) )

  proof
    cA
    cG
    cS
    cdprd
    co
    #
    wcel
    #
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    @1
    wa
    cS
    cdm
    cI
    wceq
    #
    @3
    cA
    cG
    vf
    cv
    #
    cgsu
    co
    #
    wceq
    vf
    cW
    wrex
    #
    wa
    @1
    @3
    @1
    cG
    cS
    cop
    #
    @2
    wcel
    #
    @3
    @9
    cA
    @8
    cdprd
    cfv
    @0
    cA
    @8
    cdprd
    elfvdm
    cG
    cS
    cdprd
    df-ov
    eleq2s
    cG
    cS
    @2
    df-br
    sylibr
    pm4.71ri
    @4
    @3
    @1
    @7
    @3
    @4
    @1
    @7
    wb
    @3
    @4
    wa
    #
    @1
    cA
    vf
    cW
    @6
    cmpt
    #
    crn
    #
    wcel
    @7
    @10
    @0
    @12
    cA
    cS
    vf
    vh
    vi
    cG
    cI
    cW
    c.0
    dprdval.0
    dprdval.w
    dprdval
    eleq2d
    vf
    cW
    @6
    cA
    @11
    @11
    eqid
    cG
    @5
    cgsu
    ovex
    elrnmpti
    syl6bb
    ancoms
    pm5.32da
    syl5bb
end
