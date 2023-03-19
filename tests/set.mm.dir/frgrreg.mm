include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "wo.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfrgr.mm"
include "crusgr.mm"
include "wi.mm"
include "wn.mm"
include "cn0.mm"
include "ancom.mm"
include "anbi12i.mm"
include "biimpi.mm"
include "ancomd.mm"
include "numclwwlk7lem.mm"
include "syl.mm"
include "neanior.mm"
include "cle.mm"
include "wb.mm"
include "cr.mm"
include "nn0re.mm"
include "1re.mm"
include "lenlt.mm"
include "sylancl.mm"
include "adantl.mm"
include "cn.mm"
include "elnnne0.mm"
include "nnle1eq1.mm"
include "biimpd.mm"
include "sylbir.mm"
include "a1d.mm"
include "expimpd.mm"
include "impcom.mm"
include "sylbird.mm"
include "chash.mm"
include "cfv.mm"
include "cvtx.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "simpr.mm"
include "rusgr1vtx.mm"
include "syl2an.mm"
include "orcd.mm"
include "ex.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "cv.mm"
include "cvtxdg.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "rusgrprop0.mm"
include "simp2.mm"
include "hashnncl.mm"
include "df-ne.mm"
include "nngt1ne1.mm"
include "biimprd.mm"
include "syl5bir.mm"
include "syl6bir.mm"
include "imp.mm"
include "vdgn1frgrv3.mm"
include "3imp3i2an.mm"
include "r19.26.mm"
include "wrex.mm"
include "r19.2z.mm"
include "neeq1.mm"
include "eqneqall.mm"
include "com12.mm"
include "rexlimivw.mm"
include "expd.mm"
include "com34.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "3exp.mm"
include "com15.mm"
include "com13.mm"
include "pm2.61i.mm"
include "syl6.mm"
include "com23.mm"
include "exp4b.mm"
include "simprl.mm"
include "simpl.mm"
include "ad2antlr.mm"
include "anim12ci.mm"
include "frgrreggt1.mm"
include "syl31anc.mm"
include "olcd.mm"
include "exp31.mm"
include "2a1.mm"
include "pm2.61ii.mm"

theorem frgrreg
  let cG: class G
  let cK: class K
  let cV: class V
  let vp: setvar p
  let vv: setvar v
  assume frgrreggt1.v: |- V = ( Vtx ` G )


  assert |- ( ( V e. Fin /\ V =/= (/) ) -> ( ( G e. FriendGraph /\ G RegUSGraph K ) -> ( K = 0 \/ K = 2 ) ) )

  proof
    c1
    cK
    clt
    wbr
    #
    cK
    cc0
    wceq
    #
    cK
    c2
    wceq
    #
    wo
    #
    cV
    cfn
    wcel
    #
    cV
    c0
    wne
    #
    wa
    #
    cG
    cfrgr
    wcel
    #
    cG
    cK
    crusgr
    wbr
    #
    wa
    #
    @3
    wi
    wi
    @0
    wn
    #
    @3
    wn
    #
    @6
    @9
    @3
    @6
    @9
    wa
    #
    @10
    @11
    wa
    #
    @3
    @12
    cK
    cn0
    wcel
    #
    @13
    @3
    wi
    @12
    @8
    @7
    wa
    #
    @5
    @4
    wa
    #
    wa
    @14
    @12
    @16
    @15
    @12
    @16
    @15
    wa
    @6
    @16
    @9
    @15
    @4
    @5
    ancom
    @7
    @8
    ancom
    anbi12i
    biimpi
    ancomd
    cG
    cK
    cV
    frgrreggt1.v
    numclwwlk7lem
    syl
    @13
    @14
    @12
    @3
    @11
    @10
    @14
    @12
    @3
    wi
    #
    wi
    #
    @11
    cK
    cc0
    wne
    #
    cK
    c2
    wne
    #
    wa
    #
    @10
    @18
    wi
    cK
    cc0
    cK
    c2
    neanior
    @21
    @14
    @10
    @17
    @21
    @14
    @10
    @17
    wi
    @21
    @14
    wa
    #
    @10
    cK
    c1
    wceq
    #
    @17
    @22
    @10
    cK
    c1
    cle
    wbr
    #
    @23
    @14
    @24
    @10
    wb
    #
    @21
    @14
    cK
    cr
    wcel
    c1
    cr
    wcel
    @25
    cK
    nn0re
    1re
    cK
    c1
    lenlt
    sylancl
    adantl
    @14
    @21
    @24
    @23
    wi
    #
    @14
    @19
    @20
    @26
    @14
    @19
    wa
    #
    @26
    @20
    @27
    cK
    cn
    wcel
    #
    @26
    cK
    elnnne0
    @28
    @24
    @23
    cK
    nnle1eq1
    biimpd
    sylbir
    a1d
    expimpd
    impcom
    sylbird
    cV
    chash
    cfv
    #
    c1
    wceq
    #
    @23
    @17
    wi
    @30
    @17
    @23
    @30
    @12
    @3
    @30
    @12
    wa
    @1
    @2
    @30
    cG
    cvtx
    cfv
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @8
    @1
    @12
    @30
    @33
    @29
    @32
    c1
    cV
    @31
    chash
    frgrreggt1.v
    fveq2i
    eqeq1i
    biimpi
    @9
    @8
    @6
    @7
    @8
    simpr
    #
    adantl
    cG
    cK
    rusgr1vtx
    syl2an
    orcd
    ex
    a1d
    @12
    @23
    @30
    wn
    #
    @3
    @9
    @6
    @23
    @35
    @3
    wi
    wi
    #
    @8
    @7
    @6
    @36
    wi
    #
    @8
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    w3a
    @7
    @37
    wi
    #
    vv
    @40
    cG
    cK
    cV
    frgrreggt1.v
    @40
    eqid
    rusgrprop0
    @43
    @38
    @44
    @39
    @35
    @7
    @6
    @23
    @43
    @3
    @35
    @7
    @6
    @23
    @43
    @3
    wi
    wi
    #
    @35
    @7
    @6
    w3a
    @41
    c1
    wne
    #
    vv
    cV
    wral
    #
    @45
    @35
    @7
    @6
    @7
    c1
    @29
    clt
    wbr
    #
    @47
    @35
    @7
    @6
    simp2
    @6
    @35
    @48
    @4
    @5
    @35
    @48
    wi
    #
    @4
    @5
    @29
    cn
    wcel
    #
    @49
    cV
    hashnncl
    @35
    @29
    c1
    wne
    #
    @50
    @48
    @29
    c1
    df-ne
    @50
    @48
    @51
    @29
    nngt1ne1
    biimprd
    syl5bir
    syl6bir
    imp
    impcom
    vv
    cG
    cV
    frgrreggt1.v
    vdgn1frgrv3
    3imp3i2an
    @6
    @35
    @47
    @45
    wi
    #
    @7
    @5
    @52
    @4
    @5
    @47
    @43
    @23
    @3
    @5
    @47
    @43
    @23
    @3
    wi
    #
    @47
    @43
    wa
    @46
    @42
    wa
    #
    vv
    cV
    wral
    #
    @5
    @53
    @46
    @42
    vv
    cV
    r19.26
    @5
    @55
    @53
    @5
    @55
    wa
    @54
    vv
    cV
    wrex
    @53
    @54
    vv
    cV
    r19.2z
    @54
    @53
    vv
    cV
    @54
    cK
    c1
    wne
    #
    @53
    @42
    @46
    @56
    @42
    @46
    @56
    @41
    cK
    c1
    neeq1
    biimpd
    impcom
    @23
    @56
    @3
    @3
    cK
    c1
    eqneqall
    com12
    syl
    rexlimivw
    syl
    ex
    syl5bir
    expd
    com34
    adantl
    3ad2ant3
    mpd
    3exp
    com15
    3ad2ant3
    syl
    impcom
    impcom
    com13
    pm2.61i
    syl6
    ex
    com23
    sylbir
    impcom
    com13
    mpd
    com12
    exp4b
    @0
    @6
    @9
    @3
    @0
    @6
    wa
    #
    @9
    wa
    #
    @2
    @1
    @58
    @7
    @4
    @5
    @8
    @0
    wa
    #
    @2
    @57
    @7
    @8
    simprl
    @6
    @4
    @0
    @9
    @4
    @5
    simpl
    ad2antlr
    @6
    @5
    @0
    @9
    @4
    @5
    simpr
    ad2antlr
    @57
    @0
    @9
    @8
    @0
    @6
    simpl
    @34
    anim12ci
    @7
    @4
    @5
    w3a
    @59
    @2
    cG
    cK
    cV
    frgrreggt1.v
    frgrreggt1
    imp
    syl31anc
    olcd
    exp31
    @3
    @6
    @9
    2a1
    pm2.61ii
end
