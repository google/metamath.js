include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cplt.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "clat.mm"
include "wb.mm"
include "simp13.mm"
include "cvllat.mm"
include "syl.mm"
include "simp2.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "latnle.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "simpl13.mm"
include "simprll.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latjcl.mm"
include "simprrr.mm"
include "wrex.mm"
include "simprrl.mm"
include "cal.mm"
include "simpl11.mm"
include "simpl12.mm"
include "cvlatl.mm"
include "atlrelat1.mm"
include "syl311anc.mm"
include "mpd.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "lattrd.mm"
include "simprl.mm"
include "simpll3.mm"
include "simpll2.mm"
include "cvlexch1.mm"
include "syl131anc.mm"
include "simprlr.mm"
include "cvlexchb1.mm"
include "mpbid.mm"
include "pltle.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "eqbrtrd.mm"
include "rexlimddv.mm"
include "latasymd.mm"
include "exp44.mm"
include "imp.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "cvrval2.mm"
include "sylibrd.mm"
include "simpr.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "ex.mm"
include "impbid.mm"

theorem cvlcvr1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vq: setvar q
  let vz: setvar z
  assume cvlcvr1.b: |- B = ( Base ` K )
  assume cvlcvr1.l: |- .<_ = ( le ` K )
  assume cvlcvr1.j: |- .\/ = ( join ` K )
  assume cvlcvr1.c: |- C = ( <o ` K )
  assume cvlcvr1.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. CvLat ) /\ X e. B /\ P e. A ) -> ( -. P .<_ X <-> X C ( X .\/ P ) ) )

  proof
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    clc
    wcel
    #
    w3a
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    wn
    #
    cX
    cX
    cP
    c.or
    co
    #
    cC
    wbr
    #
    @6
    @7
    cX
    @8
    cK
    cplt
    cfv
    #
    wbr
    #
    cX
    vz
    cv
    #
    @10
    wbr
    #
    @12
    @8
    c.le
    wbr
    #
    wa
    #
    @12
    @8
    wceq
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    @9
    @6
    @7
    @11
    @18
    @6
    @7
    @11
    @6
    cK
    clat
    wcel
    #
    @4
    cP
    cB
    wcel
    #
    @7
    @11
    wb
    @6
    @2
    @20
    @0
    @1
    @2
    @4
    @5
    simp13
    cK
    cvllat
    #
    syl
    #
    @3
    @4
    @5
    simp2
    #
    @5
    @3
    @21
    @4
    cA
    cB
    cP
    cK
    cvlcvr1.b
    cvlcvr1.a
    atbase
    #
    3ad2ant3
    #
    cB
    @10
    c.or
    cK
    c.le
    cX
    cP
    cvlcvr1.b
    cvlcvr1.l
    @10
    eqid
    #
    cvlcvr1.j
    latnle
    syl3anc
    #
    biimpd
    @6
    @7
    @17
    vz
    cB
    @6
    @12
    cB
    wcel
    #
    @7
    @17
    wi
    @6
    @29
    @7
    @15
    @16
    @6
    @29
    @7
    wa
    #
    @15
    wa
    #
    wa
    #
    cB
    cK
    c.le
    @12
    @8
    cvlcvr1.b
    cvlcvr1.l
    @32
    @2
    @20
    @0
    @1
    @2
    @4
    @5
    @31
    simpl13
    #
    @22
    syl
    #
    @6
    @29
    @7
    @15
    simprll
    #
    @32
    @20
    @4
    @21
    @8
    cB
    wcel
    #
    @34
    @3
    @4
    @5
    @31
    simpl2
    #
    @32
    @5
    @21
    @3
    @4
    @5
    @31
    simpl3
    @25
    syl
    cB
    c.or
    cK
    cX
    cP
    cvlcvr1.b
    cvlcvr1.j
    latjcl
    #
    syl3anc
    #
    @6
    @30
    @13
    @14
    simprrr
    #
    @32
    vq
    cv
    #
    cX
    c.le
    wbr
    wn
    #
    @41
    @12
    c.le
    wbr
    #
    wa
    #
    @8
    @12
    c.le
    wbr
    vq
    cA
    @32
    @13
    @44
    vq
    cA
    wrex
    #
    @6
    @30
    @13
    @14
    simprrl
    #
    @32
    @0
    @1
    cK
    cal
    wcel
    #
    @4
    @29
    @13
    @45
    wi
    @0
    @1
    @2
    @4
    @5
    @31
    simpl11
    #
    @0
    @1
    @2
    @4
    @5
    @31
    simpl12
    @32
    @2
    @47
    @33
    cK
    cvlatl
    syl
    @37
    @35
    cA
    cB
    @10
    cK
    c.le
    cX
    @12
    vq
    cvlcvr1.b
    cvlcvr1.l
    @27
    cvlcvr1.a
    atlrelat1
    syl311anc
    mpd
    @32
    @41
    cA
    wcel
    #
    @44
    wa
    #
    wa
    #
    @8
    cX
    @41
    c.or
    co
    #
    @12
    c.le
    @51
    cP
    @52
    c.le
    wbr
    #
    @8
    @52
    wceq
    #
    @51
    @41
    @8
    c.le
    wbr
    #
    @53
    @51
    cB
    cK
    c.le
    @41
    @12
    @8
    cvlcvr1.b
    cvlcvr1.l
    @32
    @20
    @50
    @34
    adantr
    #
    @49
    @41
    cB
    wcel
    #
    @32
    @44
    cA
    cB
    @41
    cK
    cvlcvr1.b
    cvlcvr1.a
    atbase
    ad2antrl
    #
    @32
    @29
    @50
    @35
    adantr
    #
    @32
    @36
    @50
    @39
    adantr
    @32
    @49
    @42
    @43
    simprrr
    #
    @32
    @14
    @50
    @40
    adantr
    lattrd
    @51
    @2
    @49
    @5
    @4
    @42
    @55
    @53
    wi
    @32
    @2
    @50
    @33
    adantr
    #
    @32
    @49
    @44
    simprl
    #
    @3
    @4
    @5
    @31
    @50
    simpll3
    #
    @3
    @4
    @5
    @31
    @50
    simpll2
    #
    @32
    @49
    @42
    @43
    simprrl
    cA
    cB
    @41
    cP
    c.or
    cK
    c.le
    cX
    cvlcvr1.b
    cvlcvr1.l
    cvlcvr1.j
    cvlcvr1.a
    cvlexch1
    syl131anc
    mpd
    @51
    @2
    @5
    @49
    @4
    @7
    @53
    @54
    wb
    @61
    @63
    @62
    @64
    @32
    @7
    @50
    @6
    @29
    @7
    @15
    simprlr
    adantr
    cA
    cB
    cP
    @41
    c.or
    cK
    c.le
    cX
    cvlcvr1.b
    cvlcvr1.l
    cvlcvr1.j
    cvlcvr1.a
    cvlexchb1
    syl131anc
    mpbid
    @51
    cX
    @12
    c.le
    wbr
    #
    @43
    @52
    @12
    c.le
    wbr
    #
    @32
    @65
    @50
    @32
    @13
    @65
    @46
    @32
    @0
    @4
    @29
    @13
    @65
    wi
    @48
    @37
    @35
    coml
    cB
    cB
    @10
    cK
    c.le
    cX
    @12
    cvlcvr1.l
    @27
    pltle
    syl3anc
    mpd
    adantr
    @60
    @51
    @20
    @4
    @57
    @29
    @65
    @43
    wa
    @66
    wb
    @56
    @64
    @58
    @59
    cB
    c.or
    cK
    c.le
    cX
    @41
    @12
    cvlcvr1.b
    cvlcvr1.l
    cvlcvr1.j
    latjle12
    syl13anc
    mpbi2and
    eqbrtrd
    rexlimddv
    latasymd
    exp44
    imp
    ralrimdva
    jcad
    @6
    @20
    @4
    @36
    @9
    @19
    wb
    @23
    @24
    @6
    @20
    @4
    @21
    @36
    @23
    @24
    @26
    @38
    syl3anc
    #
    vz
    clat
    cB
    cC
    @10
    cK
    c.le
    cX
    @8
    cvlcvr1.b
    cvlcvr1.l
    @27
    cvlcvr1.c
    cvrval2
    syl3anc
    sylibrd
    @6
    @9
    @11
    @7
    @6
    @9
    @11
    @6
    @9
    wa
    @20
    @4
    @36
    @9
    @11
    @6
    @20
    @9
    @23
    adantr
    @3
    @4
    @5
    @9
    simpl2
    @6
    @36
    @9
    @67
    adantr
    @6
    @9
    simpr
    clat
    cB
    cC
    @10
    cK
    cX
    @8
    cvlcvr1.b
    @27
    cvlcvr1.c
    cvrlt
    syl31anc
    ex
    @28
    sylibrd
    impbid
end
