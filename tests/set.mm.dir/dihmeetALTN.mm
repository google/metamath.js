include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "simpl1.mm"
include "simpr.mm"
include "eqid.mm"
include "dihmeetbN.mm"
include "syl112anc.mm"
include "incom.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "wn.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "adantlr.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp1r.mm"
include "simp1l3.mm"
include "simp3.mm"
include "jca.mm"
include "simp2.mm"
include "catm.mm"
include "cdvh.mm"
include "clsm.mm"
include "cjn.mm"
include "dihmeetlem20N.mm"
include "syl122anc.mm"
include "3expa.mm"
include "pm2.61dan.mm"
include "dihmeetcN.mm"
include "syl121anc.mm"

theorem dihmeetALTN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihmeetALT.b: |- B = ( Base ` K )
  assume dihmeetALT.m: |- ./\ = ( meet ` K )
  assume dihmeetALT.h: |- H = ( LHyp ` K )
  assume dihmeetALT.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cY
    c.an
    co
    #
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    wceq
    #
    @5
    @7
    wa
    #
    @9
    cY
    cX
    c.an
    co
    #
    cI
    cfv
    #
    @12
    @14
    @8
    @15
    cI
    @14
    cK
    clat
    wcel
    #
    @3
    @4
    @8
    @15
    wceq
    @14
    @0
    @17
    @0
    @1
    @3
    @4
    @7
    simpl1l
    cK
    hllat
    syl
    @2
    @3
    @4
    @7
    simpl2
    #
    @2
    @3
    @4
    @7
    simpl3
    #
    cB
    cK
    c.an
    cX
    cY
    dihmeetALT.b
    dihmeetALT.m
    latmcom
    syl3anc
    fveq2d
    @14
    @16
    @11
    @10
    cin
    #
    @12
    @14
    @2
    @4
    @3
    @7
    @16
    @20
    wceq
    @2
    @3
    @4
    @7
    simpl1
    @19
    @18
    @5
    @7
    simpr
    cB
    cH
    cI
    cK
    @6
    c.an
    cW
    cY
    cX
    dihmeetALT.b
    @6
    eqid
    #
    dihmeetALT.m
    dihmeetALT.h
    dihmeetALT.i
    dihmeetbN
    syl112anc
    @11
    @10
    incom
    syl6eq
    eqtrd
    @5
    @7
    wn
    #
    wa
    #
    @8
    cW
    @6
    wbr
    #
    @13
    @23
    @24
    wa
    cY
    cW
    @6
    wbr
    #
    @13
    @23
    @25
    @13
    @24
    @23
    @25
    wa
    @2
    @3
    @4
    @25
    @13
    @2
    @3
    @4
    @22
    @25
    simpll1
    @2
    @3
    @4
    @22
    @25
    simpll2
    @2
    @3
    @4
    @22
    @25
    simpll3
    @23
    @25
    simpr
    cB
    cH
    cI
    cK
    @6
    c.an
    cW
    cX
    cY
    dihmeetALT.b
    @21
    dihmeetALT.m
    dihmeetALT.h
    dihmeetALT.i
    dihmeetbN
    syl112anc
    adantlr
    @23
    @24
    @25
    wn
    #
    @13
    @23
    @24
    @26
    w3a
    #
    @2
    @3
    @22
    @4
    @26
    wa
    @24
    @13
    @2
    @3
    @4
    @22
    @24
    @26
    simp1l1
    @2
    @3
    @4
    @22
    @24
    @26
    simp1l2
    @5
    @22
    @24
    @26
    simp1r
    @27
    @4
    @26
    @2
    @3
    @4
    @22
    @24
    @26
    simp1l3
    @23
    @24
    @26
    simp3
    jca
    @23
    @24
    @26
    simp2
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsm
    cfv
    #
    @29
    cH
    cI
    cK
    cjn
    cfv
    #
    cK
    @6
    c.an
    cW
    cX
    cY
    dihmeetALT.b
    @21
    dihmeetALT.h
    @31
    eqid
    dihmeetALT.m
    @28
    eqid
    @29
    eqid
    @30
    eqid
    dihmeetALT.i
    dihmeetlem20N
    syl122anc
    3expa
    pm2.61dan
    @23
    @24
    wn
    #
    wa
    @2
    @3
    @4
    @32
    @13
    @2
    @3
    @4
    @22
    @32
    simpll1
    @2
    @3
    @4
    @22
    @32
    simpll2
    @2
    @3
    @4
    @22
    @32
    simpll3
    @23
    @32
    simpr
    cB
    cH
    cI
    cK
    @6
    c.an
    cW
    cX
    cY
    dihmeetALT.b
    @21
    dihmeetALT.m
    dihmeetALT.h
    dihmeetALT.i
    dihmeetcN
    syl121anc
    pm2.61dan
    pm2.61dan
end
