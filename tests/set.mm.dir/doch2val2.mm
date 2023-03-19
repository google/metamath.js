include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ccnv.mm"
include "coc.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "dochval2.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cbs.mm"
include "cops.mm"
include "simpld.mm"
include "hlop.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "a1i.mm"
include "dih1rn.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "dihintcl.mm"
include "syl12anc.mm"
include "dihcnvcl.mm"
include "opoccl.mm"
include "dochvalr2.mm"
include "opococ.mm"
include "dihcnvid2.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem doch2val2
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume doch2val2.h: |- H = ( LHyp ` K )
  assume doch2val2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume doch2val2.u: |- U = ( ( DVecH ` K ) ` W )
  assume doch2val2.v: |- V = ( Base ` U )
  assume doch2val2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume doch2val2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume doch2val2.x: |- ( ph -> X C_ V )

  disjoint H z
  disjoint I z
  disjoint K z
  disjoint V z
  disjoint W z
  disjoint X z
  assert |- ( ph -> ( ._|_ ` ( ._|_ ` X ) ) = |^| { z e. ran I | X C_ z } )

  proof
    wph
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    vz
    cv
    #
    wss
    #
    vz
    cI
    crn
    #
    crab
    #
    cint
    #
    cI
    ccnv
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    c.pe
    cfv
    #
    @8
    @7
    cfv
    #
    cI
    cfv
    #
    @5
    wph
    @0
    @9
    c.pe
    wph
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cV
    wss
    #
    @0
    @9
    wceq
    doch2val2.k
    doch2val2.x
    vz
    cU
    cH
    cI
    cK
    c.pe
    @7
    cV
    cW
    cX
    @7
    eqid
    #
    doch2val2.h
    doch2val2.i
    doch2val2.u
    doch2val2.v
    doch2val2.o
    dochval2
    syl2anc
    fveq2d
    wph
    @15
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    @12
    wceq
    doch2val2.k
    wph
    cK
    cops
    wcel
    #
    @6
    @18
    wcel
    #
    @19
    wph
    @13
    @20
    wph
    @13
    @14
    doch2val2.k
    simpld
    cK
    hlop
    syl
    #
    wph
    @15
    @5
    @3
    wcel
    #
    @21
    doch2val2.k
    wph
    @15
    @4
    @3
    wss
    #
    @4
    c0
    wne
    #
    @23
    doch2val2.k
    @24
    wph
    @2
    vz
    @3
    ssrab2
    a1i
    wph
    cV
    @4
    wcel
    #
    @25
    wph
    cV
    @3
    wcel
    #
    @16
    @26
    wph
    @15
    @27
    doch2val2.k
    cU
    cH
    cI
    cK
    cV
    cW
    doch2val2.h
    doch2val2.i
    doch2val2.u
    doch2val2.v
    dih1rn
    syl
    doch2val2.x
    @2
    @16
    vz
    cV
    @3
    @1
    cV
    cX
    sseq2
    elrab
    sylanbrc
    @4
    cV
    ne0i
    syl
    @4
    cH
    cI
    cK
    cW
    doch2val2.h
    doch2val2.i
    dihintcl
    syl12anc
    #
    @18
    cH
    cI
    cK
    cW
    @5
    @18
    eqid
    #
    doch2val2.h
    doch2val2.i
    dihcnvcl
    syl2anc
    #
    @18
    cK
    @7
    @6
    @29
    @17
    opoccl
    syl2anc
    @18
    cH
    cI
    cK
    c.pe
    @7
    cW
    @8
    @29
    @17
    doch2val2.h
    doch2val2.i
    doch2val2.o
    dochvalr2
    syl2anc
    wph
    @12
    @6
    cI
    cfv
    #
    @5
    wph
    @11
    @6
    cI
    wph
    @20
    @21
    @11
    @6
    wceq
    @22
    @30
    @18
    cK
    @7
    @6
    @29
    @17
    opococ
    syl2anc
    fveq2d
    wph
    @15
    @23
    @31
    @5
    wceq
    doch2val2.k
    @28
    cH
    cI
    cK
    cW
    @5
    doch2val2.h
    doch2val2.i
    dihcnvid2
    syl2anc
    eqtrd
    3eqtrd
end
