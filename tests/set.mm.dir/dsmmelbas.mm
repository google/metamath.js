include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfn.mm"
include "cprds.mm"
include "co.mm"
include "cbs.mm"
include "wa.mm"
include "cdsmm.mm"
include "cvv.mm"
include "wceq.mm"
include "wfn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "eqid.mm"
include "dsmmbase.mm"
include "syl.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "elrab.mm"
include "wb.mm"
include "eqtr2i.mm"
include "eleq2i.mm"
include "a1i.mm"
include "fndm.mm"
include "rabeq.mm"
include "3syl.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem dsmmelbas
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cH: class H
  let cI: class I
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume dsmmelbas.p: |- P = ( S Xs_ R )
  assume dsmmelbas.c: |- C = ( S (+)m R )
  assume dsmmelbas.b: |- B = ( Base ` P )
  assume dsmmelbas.h: |- H = ( Base ` C )
  assume dsmmelbas.i: |- ( ph -> I e. V )
  assume dsmmelbas.r: |- ( ph -> R Fn I )

  disjoint S a
  disjoint R a
  disjoint X a
  disjoint I a
  disjoint S b
  disjoint a b
  disjoint R b
  disjoint X b
  disjoint I b
  assert |- ( ph -> ( X e. H <-> ( X e. B /\ { a e. I | ( X ` a ) =/= ( 0g ` ( R ` a ) ) } e. Fin ) ) )

  proof
    wph
    cX
    cH
    wcel
    cX
    va
    cv
    #
    vb
    cv
    #
    cfv
    #
    @0
    cR
    cfv
    c0g
    cfv
    #
    wne
    #
    va
    cR
    cdm
    #
    crab
    #
    cfn
    wcel
    #
    vb
    cS
    cR
    cprds
    co
    #
    cbs
    cfv
    #
    crab
    #
    wcel
    #
    cX
    cB
    wcel
    #
    @0
    cX
    cfv
    #
    @3
    wne
    #
    va
    cI
    crab
    #
    cfn
    wcel
    #
    wa
    #
    wph
    cH
    @10
    cX
    wph
    @10
    cS
    cR
    cdsmm
    co
    #
    cbs
    cfv
    #
    cH
    wph
    cR
    cvv
    wcel
    #
    @10
    @19
    wceq
    wph
    cR
    cI
    wfn
    #
    cI
    cV
    wcel
    @20
    dsmmelbas.r
    dsmmelbas.i
    cI
    cV
    cR
    fnex
    syl2anc
    va
    @10
    cR
    cS
    vb
    cvv
    @10
    eqid
    dsmmbase
    syl
    cH
    cC
    cbs
    cfv
    @19
    dsmmelbas.h
    cC
    @18
    cbs
    dsmmelbas.c
    fveq2i
    eqtri
    syl6reqr
    eleq2d
    @11
    cX
    @9
    wcel
    #
    @14
    va
    @5
    crab
    #
    cfn
    wcel
    #
    wa
    wph
    @17
    @7
    @24
    vb
    cX
    @9
    @1
    cX
    wceq
    #
    @6
    @23
    cfn
    @25
    @4
    @14
    va
    @5
    @25
    @2
    @13
    @3
    @0
    @1
    cX
    fveq1
    neeq1d
    rabbidv
    eleq1d
    elrab
    wph
    @22
    @12
    @24
    @16
    @22
    @12
    wb
    wph
    @9
    cB
    cX
    cB
    cP
    cbs
    cfv
    @9
    dsmmelbas.b
    cP
    @8
    cbs
    dsmmelbas.p
    fveq2i
    eqtr2i
    eleq2i
    a1i
    wph
    @23
    @15
    cfn
    wph
    @21
    @5
    cI
    wceq
    @23
    @15
    wceq
    dsmmelbas.r
    cI
    cR
    fndm
    @14
    va
    @5
    cI
    rabeq
    3syl
    eleq1d
    anbi12d
    syl5bb
    bitrd
end
