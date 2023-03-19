include "wcel.mm"
include "weq.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cs3.mm"
include "ciun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wa.mm"
include "wi.mm"
include "orc.mm"
include "a1d.mm"
include "wn.mm"
include "wrex.mm"
include "eliun.mm"
include "velsn.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "cvv.mm"
include "cword.mm"
include "s3cli.mm"
include "elex.mm"
include "anim12ci.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eqwrds3.mm"
include "sylancr.mm"
include "vex.mm"
include "s3fv0.mm"
include "ax-mp.mm"
include "simp1.mm"
include "syl5eqr.mm"
include "syl6bi.mm"
include "adantr.mm"
include "sylbid.mm"
include "ancoms.mm"
include "con3d.mm"
include "exp32.mm"
include "com14.mm"
include "imp.mm"
include "expd.mm"
include "com34.mm"
include "syl5bi.mm"
include "sylnibr.mm"
include "nrexdv.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ralrimiv.mm"
include "eqidd.mm"
include "id.mm"
include "s3eqd.mm"
include "sneqd.mm"
include "cbviunv.mm"
include "eleq2i.mm"
include "notbii.mm"
include "ralbii.mm"
include "disj.mm"
include "olcd.mm"
include "pm2.61i.mm"
include "ralrimivva.mm"
include "sneq.mm"
include "difeq2d.mm"
include "iuneq12d.mm"
include "disjor.mm"

theorem s3iunsndisj
  let cB: class B
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let cA: class A
  let vd: setvar d
  let ve: setvar e
  let vs: setvar s

  disjoint B c
  disjoint X c
  disjoint Y c
  disjoint Z c
  disjoint B a
  disjoint a c
  disjoint X a
  disjoint Y a
  disjoint Z a
  disjoint A c
  disjoint A d
  disjoint c d
  disjoint B d
  disjoint X d
  disjoint Y d
  disjoint Z d
  disjoint B e
  disjoint B s
  disjoint a d
  disjoint a e
  disjoint a s
  disjoint c e
  disjoint c s
  disjoint d e
  disjoint d s
  disjoint e s
  disjoint X e
  disjoint X s
  disjoint Y e
  disjoint Y s
  disjoint Z e
  disjoint Z s
  assert |- ( B e. X -> Disj_ a e. Y U_ c e. ( Z \ { a } ) { <" a B c "> } )

  proof
    cB
    cX
    wcel
    #
    va
    vd
    weq
    #
    vc
    cZ
    va
    cv
    #
    csn
    #
    cdif
    #
    @2
    cB
    vc
    cv
    #
    cs3
    #
    csn
    #
    ciun
    #
    vc
    cZ
    vd
    cv
    #
    csn
    #
    cdif
    #
    @9
    cB
    @5
    cs3
    #
    csn
    #
    ciun
    #
    cin
    c0
    wceq
    #
    wo
    #
    vd
    cY
    wral
    va
    cY
    wral
    va
    cY
    @8
    wdisj
    @0
    @16
    va
    vd
    cY
    cY
    @1
    @0
    @2
    cY
    wcel
    #
    @9
    cY
    wcel
    #
    wa
    #
    wa
    #
    @16
    wi
    @1
    @16
    @20
    @1
    @15
    orc
    a1d
    @1
    wn
    #
    @20
    @16
    @21
    @20
    wa
    #
    @15
    @1
    @22
    vs
    cv
    #
    @14
    wcel
    #
    wn
    #
    vs
    @8
    wral
    #
    @15
    @22
    @23
    ve
    @11
    @9
    cB
    ve
    cv
    #
    cs3
    #
    csn
    #
    ciun
    #
    wcel
    #
    wn
    #
    vs
    @8
    wral
    @26
    @22
    @32
    vs
    @8
    @23
    @8
    wcel
    @23
    @7
    wcel
    #
    vc
    @4
    wrex
    @22
    @32
    vc
    @23
    @4
    @7
    eliun
    @22
    @33
    @32
    vc
    @4
    @22
    @5
    @4
    wcel
    #
    wa
    #
    @33
    @32
    @35
    @33
    wa
    #
    @23
    @29
    wcel
    #
    ve
    @11
    wrex
    @31
    @36
    @37
    ve
    @11
    @36
    @27
    @11
    wcel
    #
    wa
    @23
    @28
    wceq
    #
    @37
    @36
    @38
    @39
    wn
    #
    @35
    @33
    @38
    @40
    wi
    #
    @33
    @23
    @6
    wceq
    #
    @35
    @41
    vs
    @6
    velsn
    @22
    @34
    @42
    @41
    wi
    @22
    @34
    @38
    @42
    @40
    @22
    @34
    @38
    @42
    @40
    wi
    #
    @21
    @20
    @34
    @38
    wa
    #
    @43
    wi
    @42
    @20
    @44
    @21
    @40
    @42
    @20
    @44
    @21
    @40
    wi
    @42
    @20
    @44
    wa
    #
    wa
    @39
    @1
    @45
    @42
    @39
    @1
    wi
    @45
    @42
    wa
    @39
    @6
    @28
    wceq
    #
    @1
    @42
    @39
    @46
    wb
    @45
    @23
    @6
    @28
    eqeq1
    adantl
    @45
    @46
    @1
    wi
    @42
    @45
    @46
    @6
    chash
    cfv
    c3
    wceq
    #
    cc0
    @6
    cfv
    #
    @9
    wceq
    #
    c1
    @6
    cfv
    cB
    wceq
    #
    c2
    @6
    cfv
    @27
    wceq
    #
    w3a
    #
    wa
    #
    @1
    @45
    @6
    cvv
    cword
    wcel
    @9
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @27
    cvv
    wcel
    #
    w3a
    #
    @46
    @53
    wb
    @2
    cB
    @5
    s3cli
    @45
    @54
    @55
    wa
    #
    @56
    wa
    @57
    @20
    @58
    @44
    @56
    @0
    @55
    @19
    @54
    cB
    cX
    elex
    @18
    @54
    @17
    @9
    cY
    elex
    adantl
    anim12ci
    @38
    @56
    @34
    @27
    @11
    elex
    adantl
    anim12i
    @54
    @55
    @56
    df-3an
    sylibr
    @9
    cB
    @27
    cvv
    @6
    eqwrds3
    sylancr
    @52
    @1
    @47
    @52
    @2
    @48
    @9
    @2
    cvv
    wcel
    @48
    @2
    wceq
    va
    vex
    @2
    cB
    @5
    cvv
    s3fv0
    ax-mp
    @49
    @50
    @51
    simp1
    syl5eqr
    adantl
    syl6bi
    adantr
    sylbid
    ancoms
    con3d
    exp32
    com14
    imp
    expd
    com34
    imp
    syl5bi
    imp
    imp
    vs
    @28
    velsn
    sylnibr
    nrexdv
    ve
    @23
    @11
    @29
    eliun
    sylnibr
    ex
    rexlimdva
    syl5bi
    ralrimiv
    @25
    @32
    vs
    @8
    @24
    @31
    @14
    @30
    @23
    vc
    ve
    @11
    @13
    @29
    vc
    ve
    weq
    #
    @12
    @28
    @59
    @9
    cB
    @5
    @27
    @9
    cB
    @59
    @9
    eqidd
    @59
    cB
    eqidd
    @59
    id
    s3eqd
    sneqd
    cbviunv
    eleq2i
    notbii
    ralbii
    sylibr
    vs
    @8
    @14
    disj
    sylibr
    olcd
    ex
    pm2.61i
    ralrimivva
    cY
    @8
    @14
    va
    vd
    @1
    vc
    @4
    @11
    @7
    @13
    @1
    @3
    @10
    cZ
    @2
    @9
    sneq
    difeq2d
    @1
    @6
    @12
    @1
    @2
    cB
    @5
    @5
    @9
    cB
    @1
    id
    @1
    cB
    eqidd
    @1
    @5
    eqidd
    s3eqd
    sneqd
    iuneq12d
    disjor
    sylibr
end
