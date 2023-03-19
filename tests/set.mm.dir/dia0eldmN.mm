include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "eqid.mm"
include "op0cl.mm"
include "syl.mm"
include "lhpbase.mm"
include "op0le.mm"
include "syl2an.mm"
include "diaeldm.mm"
include "mpbir2and.mm"

theorem dia0eldmN
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume dia0eldm.z: |- .0. = ( 0. ` K )
  assume dia0eldm.h: |- H = ( LHyp ` K )
  assume dia0eldm.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> .0. e. dom I )

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
    c.0
    cI
    cdm
    wcel
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    c.0
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @2
    cK
    cops
    wcel
    #
    @4
    @0
    @7
    @1
    cK
    hlop
    #
    adantr
    @3
    cK
    c.0
    @3
    eqid
    #
    dia0eldm.z
    op0cl
    syl
    @0
    @7
    cW
    @3
    wcel
    @6
    @1
    @8
    @3
    cH
    cK
    cW
    @9
    dia0eldm.h
    lhpbase
    @3
    cK
    @5
    cW
    c.0
    @9
    @5
    eqid
    #
    dia0eldm.z
    op0le
    syl2an
    @3
    cH
    cI
    cK
    @5
    chlt
    cW
    c.0
    @9
    @10
    dia0eldm.h
    dia0eldm.i
    diaeldm
    mpbir2and
end
