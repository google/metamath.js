include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ccnv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "simpl.mm"
include "eqid.mm"
include "diadmclN.mm"
include "diadmleN.mm"
include "diass.mm"
include "syl12anc.mm"
include "docavalN.mm"
include "syldan.mm"
include "diaclN.mm"
include "intmin.mm"
include "syl.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "f1ocnvfv1.mm"
include "sylan.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"

theorem diaocN
  let cT: class T
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vz: setvar z
  assume diaoc.j: |- .\/ = ( join ` K )
  assume diaoc.m: |- ./\ = ( meet ` K )
  assume diaoc.o: |- ._|_ = ( oc ` K )
  assume diaoc.h: |- H = ( LHyp ` K )
  assume diaoc.t: |- T = ( ( LTrn ` K ) ` W )
  assume diaoc.i: |- I = ( ( DIsoA ` K ) ` W )
  assume diaoc.n: |- N = ( ( ocA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. dom I ) -> ( I ` ( ( ( ._|_ ` X ) .\/ ( ._|_ ` W ) ) ./\ W ) ) = ( N ` ( I ` X ) ) )

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
    cI
    cdm
    #
    wcel
    #
    wa
    #
    cX
    cI
    cfv
    #
    cN
    cfv
    #
    @4
    vz
    cv
    wss
    vz
    cI
    crn
    #
    crab
    cint
    #
    cI
    ccnv
    #
    cfv
    #
    c.pe
    cfv
    #
    cW
    c.pe
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cI
    cfv
    #
    cX
    c.pe
    cfv
    #
    @11
    c.or
    co
    #
    cW
    c.an
    co
    #
    cI
    cfv
    @0
    @2
    @4
    cT
    wss
    #
    @5
    @14
    wceq
    @3
    @0
    cX
    cK
    cbs
    cfv
    #
    wcel
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    @18
    @0
    @2
    simpl
    @19
    cH
    cI
    cK
    chlt
    cW
    cX
    @19
    eqid
    #
    diaoc.h
    diaoc.i
    diadmclN
    cH
    cI
    cK
    @20
    chlt
    cW
    cX
    @20
    eqid
    #
    diaoc.h
    diaoc.i
    diadmleN
    @19
    cT
    cH
    cI
    cK
    @20
    chlt
    cW
    cX
    @21
    @22
    diaoc.h
    diaoc.t
    diaoc.i
    diass
    syl12anc
    vz
    cT
    cH
    cI
    c.or
    cK
    c.an
    cN
    c.pe
    cW
    @4
    diaoc.j
    diaoc.m
    diaoc.o
    diaoc.h
    diaoc.t
    diaoc.i
    diaoc.n
    docavalN
    syldan
    @3
    @13
    @17
    cI
    @3
    @12
    @16
    cW
    c.an
    @3
    @10
    @15
    @11
    c.or
    @3
    @9
    cX
    c.pe
    @3
    @9
    @4
    @8
    cfv
    #
    cX
    @3
    @7
    @4
    @8
    @3
    @4
    @6
    wcel
    @7
    @4
    wceq
    cH
    cI
    cK
    cW
    cX
    diaoc.h
    diaoc.i
    diaclN
    vz
    @4
    @6
    intmin
    syl
    fveq2d
    @0
    @1
    @6
    cI
    wf1o
    @2
    @23
    cX
    wceq
    cH
    cI
    cK
    cW
    diaoc.h
    diaoc.i
    diaf11N
    @1
    @6
    cX
    cI
    f1ocnvfv1
    sylan
    eqtrd
    fveq2d
    oveq1d
    oveq1d
    fveq2d
    eqtr2d
end
