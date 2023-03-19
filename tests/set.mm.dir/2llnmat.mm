include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cal.mm"
include "cbs.mm"
include "simpl1.mm"
include "hlatl.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simpl2.mm"
include "eqid.mm"
include "llnbase.mm"
include "simpl3.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simprr.mm"
include "atlex.mm"
include "simp1rl.mm"
include "wb.mm"
include "simp1l.mm"
include "llncmp.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp1l3.mm"
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
include "atcvrlln2.mm"
include "syl31anc.mm"
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

theorem 2llnmat
  let cA: class A
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vp: setvar p
  assume 2llnmat.m: |- ./\ = ( meet ` K )
  assume 2llnmat.z: |- .0. = ( 0. ` K )
  assume 2llnmat.a: |- A = ( Atoms ` K )
  assume 2llnmat.n: |- N = ( LLines ` K )


  assert |- ( ( ( K e. HL /\ X e. N /\ Y e. N ) /\ ( X =/= Y /\ ( X ./\ Y ) =/= .0. ) ) -> ( X ./\ Y ) e. A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    w3a
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
    wa
    #
    vp
    cv
    #
    @5
    wceq
    #
    vp
    cA
    wrex
    #
    @5
    cA
    wcel
    @8
    @9
    @5
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
    @11
    @8
    cK
    cal
    wcel
    #
    @5
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @14
    @8
    @0
    @15
    @0
    @1
    @2
    @7
    simpl1
    #
    cK
    hlatl
    syl
    @8
    cK
    clat
    wcel
    #
    cX
    @16
    wcel
    #
    cY
    @16
    wcel
    #
    @17
    @8
    @0
    @19
    @18
    cK
    hllat
    #
    syl
    @8
    @1
    @20
    @0
    @1
    @2
    @7
    simpl2
    @16
    cK
    cN
    cX
    @16
    eqid
    #
    2llnmat.n
    llnbase
    #
    syl
    @8
    @2
    @21
    @0
    @1
    @2
    @7
    simpl3
    @16
    cK
    cN
    cY
    @23
    2llnmat.n
    llnbase
    #
    syl
    @16
    cK
    c.an
    cX
    cY
    @23
    2llnmat.m
    latmcl
    #
    syl3anc
    @3
    @4
    @6
    simprr
    vp
    cA
    @16
    cK
    @12
    @5
    c.0
    @23
    @12
    eqid
    #
    2llnmat.z
    2llnmat.a
    atlex
    syl3anc
    @8
    @13
    @10
    vp
    cA
    @8
    @9
    cA
    wcel
    #
    @13
    @10
    @8
    @28
    @13
    w3a
    #
    @5
    cX
    wne
    #
    @10
    @29
    @4
    @30
    @4
    @6
    @3
    @28
    @13
    simp1rl
    @29
    cX
    cY
    @5
    cX
    @29
    cX
    cY
    @12
    wbr
    #
    cX
    cY
    wceq
    #
    @5
    cX
    wceq
    #
    @29
    @3
    @31
    @32
    wb
    @3
    @7
    @28
    @13
    simp1l
    cK
    @12
    cN
    cX
    cY
    @27
    2llnmat.n
    llncmp
    syl
    @29
    @19
    @20
    @21
    @31
    @33
    wb
    @29
    @0
    @19
    @0
    @1
    @2
    @7
    @28
    @13
    simp1l1
    #
    @22
    syl
    #
    @29
    @1
    @20
    @0
    @1
    @2
    @7
    @28
    @13
    simp1l2
    #
    @24
    syl
    #
    @29
    @2
    @21
    @0
    @1
    @2
    @7
    @28
    @13
    simp1l3
    @25
    syl
    #
    @16
    cK
    @12
    c.an
    cX
    cY
    @23
    @27
    2llnmat.m
    latleeqm1
    syl3anc
    bitr3d
    necon3bid
    mpbid
    @29
    @9
    @5
    @5
    cX
    @29
    @10
    @33
    wo
    #
    @9
    @5
    wne
    @33
    wi
    @29
    @13
    @5
    cX
    @12
    wbr
    #
    @39
    @8
    @28
    @13
    simp3
    #
    @29
    @19
    @20
    @21
    @40
    @35
    @37
    @38
    @16
    cK
    @12
    c.an
    cX
    cY
    @23
    @27
    2llnmat.m
    latmle1
    syl3anc
    #
    @29
    cK
    cpo
    wcel
    #
    @9
    @16
    wcel
    #
    @20
    @17
    @9
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    @13
    @40
    wa
    @39
    wb
    @29
    @0
    @43
    @34
    cK
    hlpos
    syl
    @28
    @8
    @44
    @13
    cA
    @16
    @9
    cK
    @23
    2llnmat.a
    atbase
    3ad2ant2
    #
    @37
    @29
    @19
    @20
    @21
    @17
    @35
    @37
    @38
    @26
    syl3anc
    #
    @29
    @0
    @28
    @1
    @9
    cX
    @12
    wbr
    @46
    @34
    @8
    @28
    @13
    simp2
    @36
    @29
    @16
    cK
    @12
    @9
    @5
    cX
    @23
    @27
    @35
    @47
    @48
    @37
    @41
    @42
    lattrd
    cA
    @45
    @9
    cK
    @12
    cN
    cX
    @27
    @45
    eqid
    #
    2llnmat.a
    2llnmat.n
    atcvrlln2
    syl31anc
    @16
    @45
    cK
    @12
    @9
    cX
    @5
    @23
    @27
    @49
    cvrnbtwn4
    syl131anc
    mpbi2and
    @33
    @9
    @5
    neor
    sylib
    necon1d
    mpd
    3exp
    reximdvai
    mpd
    vp
    @5
    cA
    risset
    sylibr
end
