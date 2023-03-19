include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cple.mm"
include "wbr.mm"
include "cal.mm"
include "simp11.mm"
include "hlatl.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simp12.mm"
include "simp13.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "eqid.mm"
include "atlex.mm"
include "simp13l.mm"
include "wb.mm"
include "simp12l.mm"
include "simp12r.mm"
include "lncmp.mm"
include "syl12anc.mm"
include "simp111.mm"
include "simp112.mm"
include "simp113.mm"
include "latleeqm1.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "wo.mm"
include "wi.mm"
include "simp3.mm"
include "latmle1.mm"
include "cpo.mm"
include "ccvr.mm"
include "hlpos.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "lattrd.mm"
include "lncvrat.mm"
include "syl32anc.mm"
include "cvrnbtwn4.mm"
include "syl131anc.mm"
include "mpbi2and.mm"
include "neor.mm"
include "sylib.mm"
include "necon1d.mm"
include "mpd.mm"
include "3exp.mm"
include "reximdvai.mm"
include "risset.mm"
include "sylibr.mm"

theorem 2lnat
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vp: setvar p
  assume 2lnat.b: |- B = ( Base ` K )
  assume 2lnat.m: |- ./\ = ( meet ` K )
  assume 2lnat.z: |- .0. = ( 0. ` K )
  assume 2lnat.a: |- A = ( Atoms ` K )
  assume 2lnat.n: |- N = ( Lines ` K )
  assume 2lnat.f: |- F = ( pmap ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( ( F ` X ) e. N /\ ( F ` Y ) e. N ) /\ ( X =/= Y /\ ( X ./\ Y ) =/= .0. ) ) -> ( X ./\ Y ) e. A )

  proof
    cK
    chlt
    wcel
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
    cF
    cfv
    cN
    wcel
    #
    cY
    cF
    cfv
    cN
    wcel
    #
    wa
    #
    cX
    cY
    wne
    #
    cX
    cY
    c.an
    co
    #
    c.0
    wne
    #
    wa
    #
    w3a
    #
    vp
    cv
    #
    @8
    wceq
    #
    vp
    cA
    wrex
    #
    @8
    cA
    wcel
    @11
    @12
    @8
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cA
    wrex
    #
    @14
    @11
    cK
    cal
    wcel
    #
    @8
    cB
    wcel
    #
    @9
    @17
    @11
    @0
    @18
    @0
    @1
    @2
    @6
    @10
    simp11
    #
    cK
    hlatl
    syl
    @11
    cK
    clat
    wcel
    #
    @1
    @2
    @19
    @11
    @0
    @21
    @20
    cK
    hllat
    #
    syl
    @0
    @1
    @2
    @6
    @10
    simp12
    @0
    @1
    @2
    @6
    @10
    simp13
    cB
    cK
    c.an
    cX
    cY
    2lnat.b
    2lnat.m
    latmcl
    #
    syl3anc
    @3
    @6
    @7
    @9
    simp3r
    vp
    cA
    cB
    cK
    @15
    @8
    c.0
    2lnat.b
    @15
    eqid
    #
    2lnat.z
    2lnat.a
    atlex
    syl3anc
    @11
    @16
    @13
    vp
    cA
    @11
    @12
    cA
    wcel
    #
    @16
    @13
    @11
    @25
    @16
    w3a
    #
    @8
    cX
    wne
    #
    @13
    @26
    @7
    @27
    @7
    @9
    @3
    @6
    @25
    @16
    simp13l
    @26
    cX
    cY
    @8
    cX
    @26
    cX
    cY
    @15
    wbr
    #
    cX
    cY
    wceq
    #
    @8
    cX
    wceq
    #
    @26
    @3
    @4
    @5
    @28
    @29
    wb
    @3
    @6
    @10
    @25
    @16
    simp11
    @4
    @5
    @3
    @10
    @25
    @16
    simp12l
    #
    @4
    @5
    @3
    @10
    @25
    @16
    simp12r
    cB
    cK
    @15
    cF
    cN
    cX
    cY
    2lnat.b
    @24
    2lnat.n
    2lnat.f
    lncmp
    syl12anc
    @26
    @21
    @1
    @2
    @28
    @30
    wb
    @26
    @0
    @21
    @0
    @1
    @2
    @6
    @10
    @25
    @16
    simp111
    #
    @22
    syl
    #
    @0
    @1
    @2
    @6
    @10
    @25
    @16
    simp112
    #
    @0
    @1
    @2
    @6
    @10
    @25
    @16
    simp113
    #
    cB
    cK
    @15
    c.an
    cX
    cY
    2lnat.b
    @24
    2lnat.m
    latleeqm1
    syl3anc
    bitr3d
    necon3bid
    mpbid
    @26
    @12
    @8
    @8
    cX
    @26
    @13
    @30
    wo
    #
    @12
    @8
    wne
    @30
    wi
    @26
    @16
    @8
    cX
    @15
    wbr
    #
    @36
    @11
    @25
    @16
    simp3
    #
    @26
    @21
    @1
    @2
    @37
    @33
    @34
    @35
    cB
    cK
    @15
    c.an
    cX
    cY
    2lnat.b
    @24
    2lnat.m
    latmle1
    syl3anc
    #
    @26
    cK
    cpo
    wcel
    #
    @12
    cB
    wcel
    #
    @1
    @19
    @12
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    @16
    @37
    wa
    @36
    wb
    @26
    @0
    @40
    @32
    cK
    hlpos
    syl
    @25
    @11
    @41
    @16
    cA
    cB
    @12
    cK
    2lnat.b
    2lnat.a
    atbase
    3ad2ant2
    #
    @34
    @26
    @21
    @1
    @2
    @19
    @33
    @34
    @35
    @23
    syl3anc
    #
    @26
    @0
    @1
    @25
    @4
    @12
    cX
    @15
    wbr
    @43
    @32
    @34
    @11
    @25
    @16
    simp2
    @31
    @26
    cB
    cK
    @15
    @12
    @8
    cX
    2lnat.b
    @24
    @33
    @44
    @45
    @34
    @38
    @39
    lattrd
    cA
    cB
    @42
    @12
    cK
    @15
    cF
    cN
    cX
    2lnat.b
    @24
    @42
    eqid
    #
    2lnat.a
    2lnat.n
    2lnat.f
    lncvrat
    syl32anc
    cB
    @42
    cK
    @15
    @12
    cX
    @8
    2lnat.b
    @24
    @46
    cvrnbtwn4
    syl131anc
    mpbi2and
    @30
    @12
    @8
    neor
    sylib
    necon1d
    mpd
    3exp
    reximdvai
    mpd
    vp
    @8
    cA
    risset
    sylibr
end
