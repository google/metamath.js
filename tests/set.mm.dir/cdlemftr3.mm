include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wrex.mm"
include "w3a.mm"
include "wex.mm"
include "catm.mm"
include "cple.mm"
include "wbr.mm"
include "eqid.mm"
include "lhpexle3.mm"
include "df-rex.mm"
include "sylib.mm"
include "cdlemfnid.mm"
include "adantrrr.mm"
include "eqcom.mm"
include "anbi1i.mm"
include "rexbii.mm"
include "simprrr.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "rexcom4.mm"
include "anass.mm"
include "exbii.mm"
include "fvex.mm"
include "neeq1.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "r19.41v.mm"
include "3bitr3ri.mm"

theorem cdlemftr3
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  assume cdlemftr.b: |- B = ( Base ` K )
  assume cdlemftr.h: |- H = ( LHyp ` K )
  assume cdlemftr.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemftr.r: |- R = ( ( trL ` K ) ` W )

  disjoint X f
  disjoint Y f
  disjoint Z f
  disjoint H f
  disjoint K f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint B u
  disjoint f u
  disjoint X u
  disjoint Y u
  disjoint Z u
  disjoint H u
  disjoint K u
  disjoint R u
  disjoint T u
  disjoint W u
  assert |- ( ( K e. HL /\ W e. H ) -> E. f e. T ( f =/= ( _I |` B ) /\ ( ( R ` f ) =/= X /\ ( R ` f ) =/= Y /\ ( R ` f ) =/= Z ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vu
    cv
    #
    vf
    cv
    #
    cR
    cfv
    #
    wceq
    #
    @2
    cid
    cB
    cres
    wne
    #
    wa
    #
    vf
    cT
    wrex
    #
    @1
    cX
    wne
    #
    @1
    cY
    wne
    #
    @1
    cZ
    wne
    #
    w3a
    #
    wa
    #
    vu
    wex
    #
    @5
    @3
    cX
    wne
    #
    @3
    cY
    wne
    #
    @3
    cZ
    wne
    #
    w3a
    #
    wa
    #
    vf
    cT
    wrex
    #
    @0
    @1
    cK
    catm
    cfv
    #
    wcel
    #
    @1
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @11
    wa
    #
    wa
    #
    vu
    wex
    #
    @13
    @0
    @24
    vu
    @20
    wrex
    @26
    @20
    cH
    cK
    @22
    cW
    cX
    cY
    cZ
    vu
    @22
    eqid
    #
    @20
    eqid
    #
    cdlemftr.h
    lhpexle3
    @24
    vu
    @20
    df-rex
    sylib
    @0
    @25
    @12
    vu
    @0
    @25
    @12
    @0
    @25
    wa
    #
    @7
    @11
    @29
    @3
    @1
    wceq
    #
    @5
    wa
    #
    vf
    cT
    wrex
    #
    @7
    @0
    @21
    @23
    @32
    @11
    @20
    cB
    cR
    cT
    @1
    vf
    cH
    cK
    @22
    cW
    cdlemftr.b
    @27
    @28
    cdlemftr.h
    cdlemftr.t
    cdlemftr.r
    cdlemfnid
    adantrrr
    @31
    @6
    vf
    cT
    @30
    @4
    @5
    @3
    @1
    eqcom
    anbi1i
    rexbii
    sylib
    @0
    @21
    @23
    @11
    simprrr
    jca
    ex
    eximdv
    mpd
    @6
    @11
    wa
    #
    vu
    wex
    #
    vf
    cT
    wrex
    @33
    vf
    cT
    wrex
    #
    vu
    wex
    @19
    @13
    @33
    vf
    vu
    cT
    rexcom4
    @34
    @18
    vf
    cT
    @34
    @4
    @5
    @11
    wa
    #
    wa
    #
    vu
    wex
    @18
    @33
    @37
    vu
    @4
    @5
    @11
    anass
    exbii
    @36
    @18
    vu
    @3
    @2
    cR
    fvex
    @4
    @11
    @17
    @5
    @4
    @8
    @14
    @9
    @15
    @10
    @16
    @1
    @3
    cX
    neeq1
    @1
    @3
    cY
    neeq1
    @1
    @3
    cZ
    neeq1
    3anbi123d
    anbi2d
    ceqsexv
    bitri
    rexbii
    @35
    @12
    vu
    @6
    @11
    vf
    cT
    r19.41v
    exbii
    3bitr3ri
    sylib
end
