include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cdif.mm"
include "cmnf.mm"
include "cioo.mm"
include "cpnf.mm"
include "cun.mm"
include "cv.mm"
include "wn.mm"
include "eldif.mm"
include "wo.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "rexr.mm"
include "elicc1.mm"
include "syl2an.mm"
include "adantr.mm"
include "notbid.mm"
include "3anass.mm"
include "notbii.mm"
include "ianor.mm"
include "wi.mm"
include "pm2.24d.mm"
include "adantl.mm"
include "clt.mm"
include "ad2antlr.mm"
include "mnflt.mm"
include "simpr.mm"
include "simpll.mm"
include "ltnle.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "mnfxr.mm"
include "ad3antrrr.mm"
include "elioo1.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "ex.mm"
include "adantll.mm"
include "ltpnf.mm"
include "ad3antlr.mm"
include "pnfxr.mm"
include "sylancl.mm"
include "sylbird.mm"
include "orim12d.mm"
include "syl5bi.mm"
include "jaod.mm"
include "sylbid.mm"
include "expimpd.mm"
include "elun.mm"
include "syl6ibr.mm"
include "ioossre.mm"
include "unssi.mm"
include "sseli.mm"
include "elioo2.mm"
include "biimpd.mm"
include "a1i.mm"
include "com13.mm"
include "3impd.mm"
include "xrltnle.mm"
include "com3l.mm"
include "com14.mm"
include "syl.mm"
include "imp.mm"
include "sylibr.mm"
include "intnand.mm"
include "sylnibr.mm"
include "anim12i.mm"
include "mpbird.mm"
include "jca.mm"
include "impbid.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem difreicc
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR /\ B e. RR ) -> ( RR \ ( A [,] B ) ) = ( ( -oo (,) A ) u. ( B (,) +oo ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    vx
    cr
    cA
    cB
    cicc
    co
    #
    cdif
    #
    cmnf
    cA
    cioo
    co
    #
    cB
    cpnf
    cioo
    co
    #
    cun
    #
    vx
    cv
    #
    @4
    wcel
    @8
    cr
    wcel
    #
    @8
    @3
    wcel
    #
    wn
    #
    wa
    #
    @2
    @8
    @7
    wcel
    #
    @8
    cr
    @3
    eldif
    @2
    @12
    @13
    @2
    @12
    @8
    @5
    wcel
    #
    @8
    @6
    wcel
    #
    wo
    #
    @13
    @2
    @9
    @11
    @16
    @2
    @9
    wa
    #
    @11
    @8
    cxr
    wcel
    #
    cA
    @8
    cle
    wbr
    #
    @8
    cB
    cle
    wbr
    #
    w3a
    #
    wn
    #
    @16
    @17
    @10
    @21
    @2
    @10
    @21
    wb
    #
    @9
    @0
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @23
    @1
    cA
    rexr
    #
    cB
    rexr
    #
    cA
    cB
    @8
    elicc1
    #
    syl2an
    adantr
    notbid
    @22
    @18
    @19
    @20
    wa
    #
    wa
    #
    wn
    #
    @17
    @16
    @21
    @30
    @18
    @19
    @20
    3anass
    #
    notbii
    @31
    @18
    wn
    #
    @29
    wn
    #
    wo
    @17
    @16
    @18
    @29
    ianor
    @17
    @33
    @16
    @34
    @9
    @33
    @16
    wi
    @2
    @9
    @18
    @16
    @8
    rexr
    #
    pm2.24d
    adantl
    @34
    @19
    wn
    #
    @20
    wn
    #
    wo
    #
    @17
    @16
    @19
    @20
    ianor
    #
    @17
    @36
    @14
    @37
    @15
    @17
    @36
    @14
    @17
    @36
    wa
    #
    @14
    @18
    cmnf
    @8
    clt
    wbr
    #
    @8
    cA
    clt
    wbr
    #
    @9
    @18
    @2
    @36
    @35
    ad2antlr
    @9
    @41
    @2
    @36
    @8
    mnflt
    ad2antlr
    @17
    @36
    @42
    @17
    @9
    @0
    @36
    @42
    wb
    @2
    @9
    simpr
    @0
    @1
    @9
    simpll
    @9
    @0
    wa
    #
    @42
    @36
    @8
    cA
    ltnle
    #
    bicomd
    syl2anc
    biimpa
    @40
    cmnf
    cxr
    wcel
    #
    @24
    @14
    @18
    @41
    @42
    w3a
    wb
    mnfxr
    @0
    @24
    @1
    @9
    @36
    @26
    ad3antrrr
    cmnf
    cA
    @8
    elioo1
    sylancr
    mpbir3and
    ex
    @17
    @37
    cB
    @8
    clt
    wbr
    #
    @15
    @1
    @9
    @46
    @37
    wb
    @0
    cB
    @8
    ltnle
    adantll
    @17
    @46
    @15
    @17
    @46
    wa
    #
    @15
    @18
    @46
    @8
    cpnf
    clt
    wbr
    #
    @9
    @18
    @2
    @46
    @35
    ad2antlr
    @17
    @46
    simpr
    @9
    @48
    @2
    @46
    @8
    ltpnf
    ad2antlr
    @47
    @25
    cpnf
    cxr
    wcel
    #
    @15
    @18
    @46
    @48
    w3a
    #
    wb
    #
    @1
    @25
    @0
    @9
    @46
    @27
    ad3antlr
    pnfxr
    cB
    cpnf
    @8
    elioo1
    #
    sylancl
    mpbir3and
    ex
    sylbird
    orim12d
    syl5bi
    jaod
    syl5bi
    syl5bi
    sylbid
    expimpd
    @8
    @5
    @6
    elun
    #
    syl6ibr
    @2
    @13
    @12
    @2
    @13
    wa
    #
    @9
    @11
    @13
    @9
    @2
    @7
    cr
    @8
    @5
    @6
    cr
    cmnf
    cA
    ioossre
    cB
    cpnf
    ioossre
    unssi
    sseli
    adantl
    @54
    @11
    @22
    @54
    @30
    @21
    @54
    @29
    @18
    @54
    @38
    @34
    @2
    @13
    @38
    @13
    @16
    @2
    @38
    @53
    @2
    @14
    @36
    @15
    @37
    @2
    @14
    @9
    @41
    @42
    w3a
    #
    @36
    @0
    @14
    @55
    wb
    #
    @1
    @0
    @45
    @24
    @56
    mnfxr
    @26
    cmnf
    cA
    @8
    elioo2
    sylancr
    adantr
    @2
    @9
    @41
    @42
    @36
    @0
    @9
    @41
    @42
    @36
    wi
    #
    wi
    wi
    @1
    @41
    @9
    @0
    @57
    @9
    @0
    @57
    wi
    wi
    @41
    @9
    @0
    @57
    @43
    @42
    @36
    @44
    biimpd
    ex
    a1i
    com13
    adantr
    3impd
    sylbid
    @2
    @15
    @50
    @37
    @2
    @25
    @49
    @51
    @1
    @25
    @0
    @27
    adantl
    pnfxr
    @52
    sylancl
    @2
    @18
    @46
    @48
    @37
    @1
    @18
    @46
    @48
    @37
    wi
    wi
    wi
    #
    @0
    @1
    @25
    @58
    @27
    @48
    @18
    @46
    @25
    @37
    @18
    @46
    @25
    @37
    wi
    wi
    wi
    @48
    @25
    @18
    @46
    @37
    @25
    @18
    @46
    @37
    wi
    @25
    @18
    wa
    @46
    @37
    cB
    @8
    xrltnle
    biimpd
    ex
    com3l
    a1i
    com14
    syl
    adantl
    3impd
    sylbid
    orim12d
    syl5bi
    imp
    @39
    sylibr
    intnand
    @32
    sylnibr
    @54
    @24
    @25
    wa
    #
    @11
    @22
    wb
    @2
    @59
    @13
    @0
    @24
    @1
    @25
    @26
    @27
    anim12i
    adantr
    @59
    @10
    @21
    @28
    notbid
    syl
    mpbird
    jca
    ex
    impbid
    syl5bb
    eqrdv
end
