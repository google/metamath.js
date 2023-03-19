include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ckgen.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "crest.mm"
include "ccmp.mm"
include "cres.mm"
include "wi.mm"
include "cpw.mm"
include "wb.mm"
include "kgentopon.mm"
include "iscn.mm"
include "sylan.mm"
include "cin.mm"
include "wss.mm"
include "elkgen.mm"
include "ad2antrr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "adantl.mm"
include "syl5sseq.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "ralbidv.mm"
include "simpll.mm"
include "elpwi.mm"
include "resttopon.mm"
include "syl2an.mm"
include "simpllr.mm"
include "syl2anc.mm"
include "simpr.mm"
include "fssres.mm"
include "cnvresima.mm"
include "eleq1i.mm"
include "ralbii.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "r19.21v.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "ralcom.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "pm5.32da.mm"

theorem kgencn
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z

  disjoint F k
  disjoint J k
  disjoint K k
  disjoint X k
  disjoint Y k
  disjoint g k
  disjoint g x
  disjoint g z
  disjoint F g
  disjoint k x
  disjoint k z
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J x
  disjoint J z
  disjoint K g
  disjoint K x
  disjoint K z
  disjoint X g
  disjoint X x
  disjoint X z
  disjoint Y g
  disjoint Y x
  disjoint Y z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( ( kGen ` J ) Cn K ) <-> ( F : X --> Y /\ A. k e. ~P X ( ( J |`t k ) e. Comp -> ( F |` k ) e. ( ( J |`t k ) Cn K ) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    ckgen
    cfv
    #
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    vx
    cv
    #
    cima
    #
    @4
    wcel
    #
    vx
    cK
    wral
    #
    wa
    #
    @6
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    cF
    @12
    cres
    #
    @13
    cK
    ccn
    co
    wcel
    #
    wi
    #
    vk
    cX
    cpw
    #
    wral
    #
    wa
    @1
    @4
    @0
    wcel
    @2
    @5
    @11
    wb
    cJ
    cX
    kgentopon
    vx
    cF
    @4
    cK
    cX
    cY
    iscn
    sylan
    @3
    @6
    @10
    @19
    @3
    @6
    wa
    #
    @10
    @14
    @8
    @12
    cin
    #
    @13
    wcel
    #
    wi
    #
    vk
    @18
    wral
    #
    vx
    cK
    wral
    #
    @19
    @20
    @9
    @24
    vx
    cK
    @20
    @9
    @8
    cX
    wss
    #
    @24
    wa
    #
    @24
    @1
    @9
    @27
    wb
    @2
    @6
    @8
    vk
    cJ
    cX
    elkgen
    ad2antrr
    @20
    @26
    @24
    @20
    cF
    cdm
    #
    @8
    cX
    cF
    @7
    cnvimass
    @6
    @28
    cX
    wceq
    @3
    cX
    cY
    cF
    fdm
    adantl
    syl5sseq
    biantrurd
    bitr4d
    ralbidv
    @20
    @19
    @23
    vx
    cK
    wral
    #
    vk
    @18
    wral
    @25
    @20
    @17
    @29
    vk
    @18
    @20
    @12
    @18
    wcel
    #
    wa
    #
    @17
    @14
    @22
    vx
    cK
    wral
    #
    wi
    @29
    @31
    @16
    @32
    @14
    @31
    @16
    @15
    ccnv
    @7
    cima
    #
    @13
    wcel
    #
    vx
    cK
    wral
    #
    @32
    @31
    @16
    @12
    cY
    @15
    wf
    #
    @35
    wa
    #
    @35
    @31
    @13
    @12
    ctopon
    cfv
    wcel
    #
    @2
    @16
    @37
    wb
    @20
    @1
    @12
    cX
    wss
    #
    @38
    @30
    @1
    @2
    @6
    simpll
    @12
    cX
    elpwi
    #
    @12
    cJ
    cX
    resttopon
    syl2an
    @1
    @2
    @6
    @30
    simpllr
    vx
    @15
    @13
    cK
    @12
    cY
    iscn
    syl2anc
    @31
    @36
    @35
    @20
    @6
    @39
    @36
    @30
    @3
    @6
    simpr
    @40
    cX
    cY
    @12
    cF
    fssres
    syl2an
    biantrurd
    bitr4d
    @34
    @22
    vx
    cK
    @33
    @21
    @13
    @12
    @7
    cF
    cnvresima
    eleq1i
    ralbii
    syl6bb
    imbi2d
    @14
    @22
    vx
    cK
    r19.21v
    syl6bbr
    ralbidva
    @23
    vx
    vk
    cK
    @18
    ralcom
    syl6rbbr
    bitrd
    pm5.32da
    bitrd
end
