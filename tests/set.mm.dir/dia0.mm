include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ctrl.mm"
include "cple.mm"
include "wbr.mm"
include "cltrn.mm"
include "crab.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "csn.mm"
include "id.mm"
include "cal.mm"
include "hlatl.mm"
include "atl0cl.mm"
include "syl.mm"
include "adantr.mm"
include "lhpbase.mm"
include "eqid.mm"
include "atl0le.mm"
include "syl2an.mm"
include "diaval.mm"
include "syl12anc.mm"
include "wb.mm"
include "ad2antrr.mm"
include "trlcl.mm"
include "atlle0.mm"
include "syl2anc.mm"
include "trlid0b.mm"
include "bitr4d.mm"
include "rabbidva.mm"
include "idltrn.mm"
include "rabsn.mm"
include "3eqtrd.mm"

theorem dia0
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  assume dia0.b: |- B = ( Base ` K )
  assume dia0.z: |- .0. = ( 0. ` K )
  assume dia0.h: |- H = ( LHyp ` K )
  assume dia0.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> ( I ` .0. ) = { ( _I |` B ) } )

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
    #
    c.0
    cK
    cple
    cfv
    #
    wbr
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crab
    #
    @4
    cid
    cB
    cres
    #
    wceq
    #
    vf
    @9
    crab
    #
    @11
    csn
    #
    @2
    @2
    c.0
    cB
    wcel
    #
    c.0
    cW
    @7
    wbr
    #
    @3
    @10
    wceq
    @2
    id
    @0
    @15
    @1
    @0
    cK
    cal
    wcel
    #
    @15
    cK
    hlatl
    #
    cB
    cK
    c.0
    dia0.b
    dia0.z
    atl0cl
    syl
    adantr
    @0
    @17
    cW
    cB
    wcel
    @16
    @1
    @18
    cB
    cH
    cK
    cW
    dia0.b
    dia0.h
    lhpbase
    cB
    cK
    @7
    cW
    c.0
    dia0.b
    @7
    eqid
    #
    dia0.z
    atl0le
    syl2an
    cB
    @5
    @9
    vf
    cH
    cI
    cK
    @7
    chlt
    cW
    c.0
    dia0.b
    @19
    dia0.h
    @9
    eqid
    #
    @5
    eqid
    #
    dia0.i
    diaval
    syl12anc
    @2
    @8
    @12
    vf
    @9
    @2
    @4
    @9
    wcel
    #
    wa
    #
    @8
    @6
    c.0
    wceq
    #
    @12
    @23
    @17
    @6
    cB
    wcel
    @8
    @24
    wb
    @0
    @17
    @1
    @22
    @18
    ad2antrr
    cB
    @5
    @9
    @4
    cH
    cK
    cW
    dia0.b
    dia0.h
    @20
    @21
    trlcl
    cB
    cK
    @7
    @6
    c.0
    dia0.b
    @19
    dia0.z
    atlle0
    syl2anc
    cB
    @5
    @9
    @4
    cH
    cK
    cW
    c.0
    dia0.b
    dia0.z
    dia0.h
    @20
    @21
    trlid0b
    bitr4d
    rabbidva
    @2
    @11
    @9
    wcel
    @13
    @14
    wceq
    cB
    @9
    cH
    cK
    cW
    dia0.b
    dia0.h
    @20
    idltrn
    vf
    @9
    @11
    rabsn
    syl
    3eqtrd
end
