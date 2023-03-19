include "cfv.mm"
include "cdib.mm"
include "cdia.mm"
include "csn.mm"
include "cxp.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "simprd.mm"
include "lhpbase.mm"
include "syl.mm"
include "clat.mm"
include "simpld.mm"
include "hllat.mm"
include "eqid.mm"
include "latref.mm"
include "syl2anc.mm"
include "jca.mm"
include "dihvalb.mm"
include "dibval2.mm"
include "cv.mm"
include "ctrl.mm"
include "crab.mm"
include "diaval.mm"
include "wral.mm"
include "trlle.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "xpeq1d.mm"
include "3eqtrd.mm"

theorem dihwN
  let wph: wff ph
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vg: setvar g
  assume dihw.b: |- B = ( Base ` K )
  assume dihw.h: |- H = ( LHyp ` K )
  assume dihw.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihw.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume dihw.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihw.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint K f
  disjoint W f
  disjoint f g
  disjoint K g
  disjoint T g
  disjoint W g
  disjoint g ph
  assert |- ( ph -> ( I ` W ) = ( T X. { .0. } ) )

  proof
    wph
    cW
    cI
    cfv
    #
    cW
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    cW
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    c.0
    csn
    #
    cxp
    #
    cT
    @5
    cxp
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
    cW
    cB
    wcel
    #
    cW
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    wa
    #
    @0
    @2
    wceq
    dihw.k
    wph
    @10
    @12
    wph
    @8
    @10
    wph
    @7
    @8
    dihw.k
    simprd
    cB
    cH
    cK
    cW
    dihw.b
    dihw.h
    lhpbase
    syl
    #
    wph
    cK
    clat
    wcel
    #
    @10
    @12
    wph
    @7
    @15
    wph
    @7
    @8
    dihw.k
    simpld
    cK
    hllat
    syl
    @14
    cB
    cK
    @11
    cW
    dihw.b
    @11
    eqid
    #
    latref
    syl2anc
    jca
    #
    cB
    @1
    cH
    cI
    cK
    @11
    chlt
    cW
    cW
    dihw.b
    @16
    dihw.h
    dihw.i
    @1
    eqid
    #
    dihvalb
    syl2anc
    wph
    @9
    @13
    @2
    @6
    wceq
    dihw.k
    @17
    cB
    cT
    vf
    cH
    @1
    @3
    cK
    @11
    chlt
    cW
    cW
    c.0
    dihw.b
    @16
    dihw.h
    dihw.t
    dihw.o
    @3
    eqid
    #
    @18
    dibval2
    syl2anc
    wph
    @4
    cT
    @5
    wph
    @4
    vg
    cv
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    cW
    @11
    wbr
    #
    vg
    cT
    crab
    #
    cT
    wph
    @9
    @13
    @4
    @23
    wceq
    dihw.k
    @17
    cB
    @21
    cT
    vg
    cH
    @3
    cK
    @11
    chlt
    cW
    cW
    dihw.b
    @16
    dihw.h
    dihw.t
    @21
    eqid
    #
    @19
    diaval
    syl2anc
    wph
    @22
    vg
    cT
    wral
    cT
    @23
    wceq
    wph
    @22
    vg
    cT
    wph
    @9
    @20
    cT
    wcel
    @22
    dihw.k
    @21
    cT
    @20
    cH
    cK
    @11
    cW
    @16
    dihw.h
    dihw.t
    @24
    trlle
    sylan
    ralrimiva
    @22
    vg
    cT
    rabid2
    sylibr
    eqtr4d
    xpeq1d
    3eqtrd
end
