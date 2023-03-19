include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "cin.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "clat.mm"
include "csn.mm"
include "simpl1.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprl.mm"
include "inss2.mm"
include "sseli.mm"
include "syl6eleq.mm"
include "ad2antll.mm"
include "elpaddatiN.mm"
include "syl32anc.mm"
include "simp1.mm"
include "simp3l.mm"
include "inss1.mm"
include "simp2r.mm"
include "sseldi.mm"
include "simp3r.mm"
include "pexmidlem3N.mm"
include "syl121anc.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem pexmidlem4N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  assume pexmidlem.l: |- .<_ = ( le ` K )
  assume pexmidlem.j: |- .\/ = ( join ` K )
  assume pexmidlem.a: |- A = ( Atoms ` K )
  assume pexmidlem.p: |- .+ = ( +P ` K )
  assume pexmidlem.o: |- ._|_ = ( _|_P ` K )
  assume pexmidlem.m: |- M = ( X .+ { p } )

  disjoint A q
  disjoint K q
  disjoint M q
  disjoint ._|_ q
  disjoint .+ q
  disjoint X q
  disjoint p q
  disjoint q r
  disjoint A r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint M r
  disjoint ._|_ r
  disjoint .+ r
  disjoint X r
  disjoint p r
  assert |- ( ( ( K e. HL /\ X C_ A /\ p e. A ) /\ ( X =/= (/) /\ q e. ( ( ._|_ ` X ) i^i M ) ) ) -> p e. ( X .+ ( ._|_ ` X ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    vp
    cv
    #
    cA
    wcel
    #
    w3a
    #
    cX
    c0
    wne
    #
    vq
    cv
    #
    cX
    c.pe
    cfv
    #
    cM
    cin
    #
    wcel
    #
    wa
    #
    wa
    #
    @6
    vr
    cv
    #
    @2
    c.or
    co
    c.le
    wbr
    #
    vr
    cX
    wrex
    #
    @2
    cX
    @7
    c.pl
    co
    wcel
    #
    @11
    cK
    clat
    wcel
    #
    @1
    @3
    @5
    @6
    cX
    @2
    csn
    c.pl
    co
    #
    wcel
    #
    @14
    @11
    @0
    @16
    @0
    @1
    @3
    @10
    simpl1
    cK
    hllat
    syl
    @0
    @1
    @3
    @10
    simpl2
    @0
    @1
    @3
    @10
    simpl3
    @4
    @5
    @9
    simprl
    @9
    @18
    @4
    @5
    @9
    @6
    cM
    @17
    @8
    cM
    @6
    @7
    cM
    inss2
    sseli
    pexmidlem.m
    syl6eleq
    ad2antll
    cA
    c.pl
    @2
    @6
    c.or
    cK
    c.le
    cX
    vr
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    elpaddatiN
    syl32anc
    @11
    @13
    @15
    vr
    cX
    @11
    @12
    cX
    wcel
    #
    @13
    @15
    @4
    @10
    @19
    @13
    wa
    #
    @15
    @4
    @10
    @20
    w3a
    #
    @4
    @19
    @6
    @7
    wcel
    @13
    @15
    @4
    @10
    @20
    simp1
    @4
    @10
    @19
    @13
    simp3l
    @21
    @8
    @7
    @6
    @7
    cM
    inss1
    @4
    @5
    @9
    @20
    simp2r
    sseldi
    @4
    @10
    @19
    @13
    simp3r
    cA
    c.pl
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    vr
    vq
    vp
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    pexmidlem.o
    pexmidlem.m
    pexmidlem3N
    syl121anc
    3expia
    expd
    rexlimdv
    mpd
end
