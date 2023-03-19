include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "eqid.mm"
include "lhpbase.mm"
include "adantl.mm"
include "clat.mm"
include "hllat.mm"
include "latref.mm"
include "syl2an.mm"
include "diaeldm.mm"
include "mpbir2and.mm"

theorem dia1eldmN
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume dia1eldm.h: |- H = ( LHyp ` K )
  assume dia1eldm.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> W e. dom I )

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
    cW
    cI
    cdm
    wcel
    cW
    cK
    cbs
    cfv
    #
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
    @1
    @3
    @0
    @2
    cH
    cK
    cW
    @2
    eqid
    #
    dia1eldm.h
    lhpbase
    #
    adantl
    @0
    cK
    clat
    wcel
    @3
    @5
    @1
    cK
    hllat
    @7
    @2
    cK
    @4
    cW
    @6
    @4
    eqid
    #
    latref
    syl2an
    @2
    cH
    cI
    cK
    @4
    chlt
    cW
    cW
    @6
    @8
    dia1eldm.h
    dia1eldm.i
    diaeldm
    mpbir2and
end
