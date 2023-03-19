include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wfn.mm"
include "coc.mm"
include "cfv.mm"
include "wceq.mm"
include "cltrn.mm"
include "crio.mm"
include "ctendo.mm"
include "copab.mm"
include "cmpt.mm"
include "cvv.mm"
include "wral.mm"
include "breq1.mm"
include "notbid.mm"
include "elrab.mm"
include "eqid.mm"
include "dicval.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "syl.mm"
include "dicfval.mm"
include "fneq1d.mm"
include "mpbird.mm"

theorem dicfnN
  let cA: class A
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vf: setvar f
  let vs: setvar s
  let vu: setvar u
  assume dicfn.l: |- .<_ = ( le ` K )
  assume dicfn.a: |- A = ( Atoms ` K )
  assume dicfn.h: |- H = ( LHyp ` K )
  assume dicfn.i: |- I = ( ( DIsoC ` K ) ` W )

  disjoint .<_ p
  disjoint A p
  disjoint K p
  disjoint W p
  disjoint p q
  disjoint .<_ q
  disjoint A q
  disjoint H q
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f u
  disjoint K f
  disjoint p s
  disjoint p u
  disjoint q s
  disjoint q u
  disjoint K q
  disjoint s u
  disjoint K s
  disjoint K u
  disjoint W f
  disjoint W q
  disjoint W s
  disjoint W u
  disjoint V q
  assert |- ( ( K e. V /\ W e. H ) -> I Fn { p e. A | -. p .<_ W } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    vp
    cA
    crab
    #
    wfn
    vq
    @4
    vf
    cv
    cW
    cK
    coc
    cfv
    cfv
    #
    vu
    cv
    cfv
    vq
    cv
    #
    wceq
    vu
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crio
    vs
    cv
    #
    cfv
    wceq
    @8
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    wa
    vf
    vs
    copab
    #
    cmpt
    #
    @4
    wfn
    #
    @0
    @10
    cvv
    wcel
    #
    vq
    @4
    wral
    @12
    @0
    @13
    vq
    @4
    @6
    @4
    wcel
    @0
    @6
    cA
    wcel
    @6
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @13
    @3
    @15
    vp
    @6
    cA
    @1
    @6
    wceq
    @2
    @14
    @1
    @6
    cW
    c.le
    breq1
    notbid
    elrab
    @0
    @16
    wa
    @10
    @6
    cI
    cfv
    cvv
    cA
    @5
    @6
    @7
    vf
    vu
    @9
    cH
    cI
    cK
    c.le
    cV
    cW
    vs
    dicfn.l
    dicfn.a
    dicfn.h
    @5
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    dicfn.i
    dicval
    @6
    cI
    fvex
    syl6eqelr
    sylan2b
    ralrimiva
    vq
    @4
    @10
    @11
    cvv
    @11
    eqid
    fnmpt
    syl
    @0
    @4
    cI
    @11
    cA
    @5
    @7
    vf
    vu
    @9
    cH
    cI
    cK
    c.le
    cV
    cW
    vs
    vp
    vq
    dicfn.l
    dicfn.a
    dicfn.h
    @17
    @18
    @19
    dicfn.i
    dicfval
    fneq1d
    mpbird
end
