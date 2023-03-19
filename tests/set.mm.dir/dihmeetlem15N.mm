include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "cfv.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpr1.mm"
include "simpl3.mm"
include "simpl3r.mm"
include "weq.mm"
include "simp3.mm"
include "simp22.mm"
include "eqbrtrrd.mm"
include "clat.mm"
include "wb.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp13l.mm"
include "atbase.mm"
include "simp12.mm"
include "latleeqm2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simp23.mm"
include "3expia.mm"
include "necon3bd.mm"
include "mpd.mm"
include "coc.mm"
include "cltrn.mm"
include "ctendo.mm"
include "crio.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "eqid.mm"
include "dihmeetlem13N.mm"
include "syl121anc.mm"

theorem dihmeetlem15N
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vr: setvar r
  let vp: setvar p
  let vh: setvar h
  assume dihmeetlem14.b: |- B = ( Base ` K )
  assume dihmeetlem14.l: |- .<_ = ( le ` K )
  assume dihmeetlem14.h: |- H = ( LHyp ` K )
  assume dihmeetlem14.j: |- .\/ = ( join ` K )
  assume dihmeetlem14.m: |- ./\ = ( meet ` K )
  assume dihmeetlem14.a: |- A = ( Atoms ` K )
  assume dihmeetlem14.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem14.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem14.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihmeetlem15.z: |- .0. = ( 0g ` U )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ Y e. B /\ ( p e. A /\ -. p .<_ W ) ) /\ ( ( r e. A /\ -. r .<_ W ) /\ r .<_ Y /\ ( Y ./\ p ) .<_ W ) ) -> ( ( I ` r ) i^i ( I ` p ) ) = { .0. } )

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
    cY
    cB
    wcel
    #
    vp
    cv
    #
    cA
    wcel
    #
    @4
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    vr
    cv
    #
    cA
    wcel
    @10
    cW
    c.le
    wbr
    wn
    wa
    #
    @10
    cY
    c.le
    wbr
    #
    cY
    @4
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @2
    @11
    @8
    @10
    @4
    wne
    #
    @10
    cI
    cfv
    @4
    cI
    cfv
    cin
    c.0
    csn
    wceq
    @2
    @3
    @8
    @15
    simpl1
    @9
    @11
    @12
    @14
    simpr1
    @2
    @3
    @8
    @15
    simpl3
    @16
    @7
    @17
    @5
    @7
    @2
    @3
    @15
    simpl3r
    @16
    @6
    @10
    @4
    @9
    @15
    vr
    vp
    weq
    #
    @6
    @9
    @15
    @18
    w3a
    #
    @13
    @4
    cW
    c.le
    @19
    @4
    cY
    c.le
    wbr
    #
    @13
    @4
    wceq
    #
    @19
    @10
    @4
    cY
    c.le
    @9
    @15
    @18
    simp3
    @9
    @11
    @12
    @14
    @18
    simp22
    eqbrtrrd
    @19
    cK
    clat
    wcel
    #
    @4
    cB
    wcel
    #
    @3
    @20
    @21
    wb
    @19
    @0
    @22
    @0
    @1
    @3
    @8
    @15
    @18
    simp11l
    cK
    hllat
    syl
    @19
    @5
    @23
    @5
    @7
    @2
    @3
    @15
    @18
    simp13l
    cA
    cB
    @4
    cK
    dihmeetlem14.b
    dihmeetlem14.a
    atbase
    syl
    @2
    @3
    @8
    @15
    @18
    simp12
    cB
    cK
    c.le
    c.an
    @4
    cY
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.m
    latleeqm2
    syl3anc
    mpbid
    @9
    @11
    @12
    @14
    @18
    simp23
    eqbrtrrd
    3expia
    necon3bd
    mpd
    cA
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    @10
    @4
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    vh
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @24
    vh
    cv
    cfv
    #
    @10
    wceq
    vh
    @25
    crio
    #
    @27
    @4
    wceq
    vh
    @25
    crio
    #
    cH
    cI
    c.or
    cK
    c.le
    vh
    @25
    cid
    cB
    cres
    cmpt
    #
    cW
    c.0
    dihmeetlem14.b
    dihmeetlem14.l
    dihmeetlem14.j
    dihmeetlem14.a
    dihmeetlem14.h
    @24
    eqid
    @25
    eqid
    @26
    eqid
    @30
    eqid
    dihmeetlem14.i
    dihmeetlem14.u
    dihmeetlem15.z
    @28
    eqid
    @29
    eqid
    dihmeetlem13N
    syl121anc
end
