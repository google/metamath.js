include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ctrl.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "cbs.mm"
include "wceq.mm"
include "id.mm"
include "eqid.mm"
include "lhpbase.mm"
include "adantl.mm"
include "clat.mm"
include "hllat.mm"
include "latref.mm"
include "syl2an.mm"
include "diaval.mm"
include "syl12anc.mm"
include "wral.mm"
include "trlle.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqtr4d.mm"

theorem dia1N
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume dia1.h: |- H = ( LHyp ` K )
  assume dia1.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia1.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> ( I ` W ) = T )

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
    #
    cW
    cI
    cfv
    #
    vf
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
    cK
    cple
    cfv
    #
    wbr
    #
    vf
    cT
    crab
    #
    cT
    @2
    @2
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    cW
    @6
    wbr
    #
    @3
    @8
    wceq
    @2
    id
    @1
    @10
    @0
    @9
    cH
    cK
    cW
    @9
    eqid
    #
    dia1.h
    lhpbase
    #
    adantl
    @0
    cK
    clat
    wcel
    @10
    @11
    @1
    cK
    hllat
    @13
    @9
    cK
    @6
    cW
    @12
    @6
    eqid
    #
    latref
    syl2an
    @9
    @5
    cT
    vf
    cH
    cI
    cK
    @6
    chlt
    cW
    cW
    @12
    @14
    dia1.h
    dia1.t
    @5
    eqid
    #
    dia1.i
    diaval
    syl12anc
    @2
    @7
    vf
    cT
    wral
    cT
    @8
    wceq
    @2
    @7
    vf
    cT
    @5
    cT
    @4
    cH
    cK
    @6
    cW
    @14
    dia1.h
    dia1.t
    @15
    trlle
    ralrimiva
    @7
    vf
    cT
    rabid2
    sylibr
    eqtr4d
end
