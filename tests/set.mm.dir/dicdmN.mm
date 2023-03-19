include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "dicfnN.mm"
include "fndm.mm"
include "syl.mm"

theorem dicdmN
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
  assert |- ( ( K e. V /\ W e. H ) -> dom I = { p e. A | -. p .<_ W } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cI
    vp
    cv
    cW
    c.le
    wbr
    wn
    vp
    cA
    crab
    #
    wfn
    cI
    cdm
    @0
    wceq
    cA
    cH
    cI
    cK
    c.le
    cV
    cW
    vp
    dicfn.l
    dicfn.a
    dicfn.h
    dicfn.i
    dicfnN
    @0
    cI
    fndm
    syl
end
