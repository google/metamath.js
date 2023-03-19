include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "simpl1.mm"
include "clat.mm"
include "atllat.mm"
include "3ad2ant1.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr.mm"
include "atlex.mm"
include "wi.mm"
include "wb.mm"
include "syl.mm"
include "adantl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "atcmp.mm"
include "breq1.mm"
include "biimpd.mm"
include "syl6bi.mm"
include "impd.mm"
include "sylbird.mm"
include "adantlr.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "necon1bd.mm"
include "atn0.mm"
include "3adant3.mm"
include "latleeqm1.mm"
include "eqeq1.mm"
include "biimpcd.mm"
include "sylbid.mm"
include "necon3ad.mm"
include "mpid.mm"
include "impbid.mm"

theorem atnle
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  assume atnle.b: |- B = ( Base ` K )
  assume atnle.l: |- .<_ = ( le ` K )
  assume atnle.m: |- ./\ = ( meet ` K )
  assume atnle.z: |- .0. = ( 0. ` K )
  assume atnle.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A /\ X e. B ) -> ( -. P .<_ X <-> ( P ./\ X ) = .0. ) )

  proof
    cK
    cal
    wcel
    #
    cP
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    wn
    #
    cP
    cX
    c.an
    co
    #
    c.0
    wceq
    #
    @3
    @4
    @6
    c.0
    @3
    @6
    c.0
    wne
    #
    @4
    @3
    @8
    wa
    #
    vy
    cv
    #
    @6
    c.le
    wbr
    #
    vy
    cA
    wrex
    #
    @4
    @9
    @0
    @6
    cB
    wcel
    #
    @8
    @12
    @0
    @1
    @2
    @8
    simpl1
    @3
    @13
    @8
    @3
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @2
    @13
    @0
    @1
    @14
    @2
    cK
    atllat
    #
    3ad2ant1
    #
    @1
    @0
    @15
    @2
    cA
    cB
    cP
    cK
    atnle.b
    atnle.a
    atbase
    #
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    cB
    cK
    c.an
    cP
    cX
    atnle.b
    atnle.m
    latmcl
    syl3anc
    adantr
    @3
    @8
    simpr
    vy
    cA
    cB
    cK
    c.le
    @6
    c.0
    atnle.b
    atnle.l
    atnle.z
    atnle.a
    atlex
    syl3anc
    @9
    @11
    @4
    vy
    cA
    @3
    @10
    cA
    wcel
    #
    @11
    @4
    wi
    @8
    @3
    @21
    wa
    #
    @11
    @10
    cP
    c.le
    wbr
    #
    @10
    cX
    c.le
    wbr
    #
    wa
    #
    @4
    @22
    @14
    @10
    cB
    wcel
    #
    @15
    @2
    @25
    @11
    wb
    @22
    @0
    @14
    @0
    @1
    @2
    @21
    simpl1
    #
    @16
    syl
    @21
    @26
    @3
    cA
    cB
    @10
    cK
    atnle.b
    atnle.a
    atbase
    adantl
    @22
    @1
    @15
    @0
    @1
    @2
    @21
    simpl2
    #
    @18
    syl
    @0
    @1
    @2
    @21
    simpl3
    cB
    cK
    c.le
    c.an
    @10
    cP
    cX
    atnle.b
    atnle.l
    atnle.m
    latlem12
    syl13anc
    @22
    @23
    @24
    @4
    @22
    @23
    @10
    cP
    wceq
    #
    @24
    @4
    wi
    @22
    @0
    @21
    @1
    @23
    @29
    wb
    @27
    @3
    @21
    simpr
    @28
    cA
    @10
    cP
    cK
    c.le
    atnle.l
    atnle.a
    atcmp
    syl3anc
    @29
    @24
    @4
    @10
    cP
    cX
    c.le
    breq1
    biimpd
    syl6bi
    impd
    sylbird
    adantlr
    rexlimdva
    mpd
    ex
    necon1bd
    @3
    @7
    cP
    c.0
    wne
    #
    @5
    @0
    @1
    @30
    @2
    cA
    cP
    cK
    c.0
    atnle.z
    atnle.a
    atn0
    3adant3
    @3
    @7
    @30
    @5
    wi
    @3
    @7
    wa
    #
    @4
    cP
    c.0
    @31
    @4
    @6
    cP
    wceq
    #
    cP
    c.0
    wceq
    #
    @3
    @4
    @32
    wb
    #
    @7
    @3
    @14
    @15
    @2
    @34
    @17
    @19
    @20
    cB
    cK
    c.le
    c.an
    cP
    cX
    atnle.b
    atnle.l
    atnle.m
    latleeqm1
    syl3anc
    adantr
    @7
    @32
    @33
    wi
    @3
    @32
    @7
    @33
    @6
    cP
    c.0
    eqeq1
    biimpcd
    adantl
    sylbid
    necon3ad
    ex
    mpid
    impbid
end
