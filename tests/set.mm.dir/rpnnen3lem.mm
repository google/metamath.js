include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cq.mm"
include "crab.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "qbtwnre.mm"
include "wn.mm"
include "simp2.mm"
include "simp3r.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "simp11.mm"
include "qre.mm"
include "3ad2ant2.mm"
include "simp3l.mm"
include "ltnsymd.mm"
include "intnand.mm"
include "sylnibr.mm"
include "nelne1.mm"
include "syl2anc.mm"
include "necomd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "3expa.mm"

theorem rpnnen3lem
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint a d
  disjoint b d
  disjoint c d
  assert |- ( ( ( a e. RR /\ b e. RR ) /\ a < b ) -> { c e. QQ | c < a } =/= { c e. QQ | c < b } )

  proof
    va
    cv
    #
    cr
    wcel
    #
    vb
    cv
    #
    cr
    wcel
    #
    @0
    @2
    clt
    wbr
    #
    vc
    cv
    #
    @0
    clt
    wbr
    #
    vc
    cq
    crab
    #
    @5
    @2
    clt
    wbr
    #
    vc
    cq
    crab
    #
    wne
    #
    @1
    @3
    @4
    w3a
    #
    @0
    vd
    cv
    #
    clt
    wbr
    #
    @12
    @2
    clt
    wbr
    #
    wa
    #
    vd
    cq
    wrex
    @10
    vd
    @0
    @2
    qbtwnre
    @11
    @15
    @10
    vd
    cq
    @11
    @12
    cq
    wcel
    #
    @15
    w3a
    #
    @9
    @7
    @17
    @12
    @9
    wcel
    #
    @12
    @7
    wcel
    #
    wn
    @9
    @7
    wne
    @17
    @16
    @14
    @18
    @11
    @16
    @15
    simp2
    @11
    @16
    @13
    @14
    simp3r
    @8
    @14
    vc
    @12
    cq
    @5
    @12
    @2
    clt
    breq1
    elrab
    sylanbrc
    @17
    @16
    @12
    @0
    clt
    wbr
    #
    wa
    @19
    @17
    @20
    @16
    @17
    @0
    @12
    @1
    @3
    @4
    @16
    @15
    simp11
    @16
    @11
    @12
    cr
    wcel
    @15
    @12
    qre
    3ad2ant2
    @11
    @16
    @13
    @14
    simp3l
    ltnsymd
    intnand
    @6
    @20
    vc
    @12
    cq
    @5
    @12
    @0
    clt
    breq1
    elrab
    sylnibr
    @12
    @9
    @7
    nelne1
    syl2anc
    necomd
    rexlimdv3a
    mpd
    3expa
end
