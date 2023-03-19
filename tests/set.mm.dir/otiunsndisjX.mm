include "wcel.mm"
include "weq.mm"
include "cv.mm"
include "cotp.mm"
include "csn.mm"
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
include "w3a.mm"
include "wb.mm"
include "simprl.mm"
include "adantl.mm"
include "simpl.mm"
include "otthg.mm"
include "syl3anc.mm"
include "simp1.mm"
include "syl6bi.mm"
include "con3d.mm"
include "ex.mm"
include "com13.mm"
include "imp31.mm"
include "adantr.mm"
include "velsn.mm"
include "eqeq1.mm"
include "notbid.mm"
include "sylbi.mm"
include "mpbird.mm"
include "sylnibr.mm"
include "nrexdv.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "oteq3.mm"
include "sneqd.mm"
include "cbviunv.mm"
include "eleq2i.mm"
include "notbii.mm"
include "ralbii.mm"
include "sylibr.mm"
include "disj.mm"
include "olcd.mm"
include "pm2.61i.mm"
include "ralrimivva.mm"
include "oteq1.mm"
include "iuneq2d.mm"
include "disjor.mm"

theorem otiunsndisjX
  let cB: class B
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x

  disjoint B a
  disjoint B c
  disjoint a c
  disjoint V a
  disjoint V c
  disjoint W a
  disjoint W c
  disjoint X a
  disjoint X c
  disjoint B d
  disjoint B e
  disjoint B s
  disjoint a d
  disjoint a e
  disjoint a s
  disjoint c d
  disjoint c e
  disjoint c s
  disjoint d e
  disjoint d s
  disjoint e s
  disjoint V d
  disjoint V e
  disjoint V s
  disjoint W d
  disjoint W e
  disjoint W s
  disjoint X d
  disjoint X e
  disjoint X s
  disjoint k x
  assert |- ( B e. X -> Disj_ a e. V U_ c e. W { <. a , B , c >. } )

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
    cW
    va
    cv
    #
    cB
    vc
    cv
    #
    cotp
    #
    csn
    #
    ciun
    #
    vc
    cW
    vd
    cv
    #
    cB
    @3
    cotp
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
    cV
    wral
    va
    cV
    wral
    va
    cV
    @6
    wdisj
    @0
    @12
    va
    vd
    cV
    cV
    @1
    @0
    @2
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    wa
    #
    wa
    #
    @12
    wi
    @1
    @12
    @16
    @1
    @11
    orc
    a1d
    @1
    wn
    #
    @16
    @12
    @17
    @16
    wa
    #
    @11
    @1
    @18
    vs
    cv
    #
    @10
    wcel
    #
    wn
    #
    vs
    @6
    wral
    #
    @11
    @18
    @19
    ve
    cW
    @7
    cB
    ve
    cv
    #
    cotp
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
    @6
    wral
    @22
    @18
    @28
    vs
    @6
    @19
    @6
    wcel
    @19
    @5
    wcel
    #
    vc
    cW
    wrex
    @18
    @28
    vc
    @19
    cW
    @5
    eliun
    @18
    @29
    @28
    vc
    cW
    @18
    @3
    cW
    wcel
    #
    wa
    #
    @29
    @28
    @31
    @29
    wa
    #
    @19
    @25
    wcel
    #
    ve
    cW
    wrex
    @27
    @32
    @33
    ve
    cW
    @32
    @23
    cW
    wcel
    #
    wa
    #
    @19
    @24
    wceq
    #
    @33
    @35
    @36
    wn
    #
    @4
    @24
    wceq
    #
    wn
    #
    @32
    @39
    @34
    @31
    @39
    @29
    @17
    @16
    @30
    @39
    @30
    @16
    @17
    @39
    @30
    @16
    @17
    @39
    wi
    @30
    @16
    wa
    #
    @38
    @1
    @40
    @38
    @1
    cB
    cB
    wceq
    #
    vc
    ve
    weq
    #
    w3a
    #
    @1
    @40
    @13
    @0
    @30
    @38
    @43
    wb
    @16
    @13
    @30
    @0
    @13
    @14
    simprl
    adantl
    @30
    @0
    @15
    simprl
    @30
    @16
    simpl
    @2
    cB
    @3
    @7
    cV
    cB
    @23
    cX
    cW
    otthg
    syl3anc
    @1
    @41
    @42
    simp1
    syl6bi
    con3d
    ex
    com13
    imp31
    adantr
    adantr
    @32
    @37
    @39
    wb
    #
    @34
    @29
    @44
    @31
    @29
    @19
    @4
    wceq
    #
    @44
    vs
    @4
    velsn
    @45
    @36
    @38
    @19
    @4
    @24
    eqeq1
    notbid
    sylbi
    adantl
    adantr
    mpbird
    vs
    @24
    velsn
    sylnibr
    nrexdv
    ve
    @19
    cW
    @25
    eliun
    sylnibr
    ex
    rexlimdva
    syl5bi
    ralrimiv
    @21
    @28
    vs
    @6
    @20
    @27
    @10
    @26
    @19
    vc
    ve
    cW
    @9
    @25
    @42
    @8
    @24
    @3
    @23
    @7
    cB
    oteq3
    sneqd
    cbviunv
    eleq2i
    notbii
    ralbii
    sylibr
    vs
    @6
    @10
    disj
    sylibr
    olcd
    ex
    pm2.61i
    ralrimivva
    cV
    @6
    @10
    va
    vd
    @1
    vc
    cW
    @5
    @9
    @1
    @4
    @8
    @2
    @7
    cB
    @3
    oteq1
    sneqd
    iuneq2d
    disjor
    sylibr
end
