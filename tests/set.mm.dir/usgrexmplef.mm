include "cdm.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cun.mm"
include "wf1o.mm"
include "wf1.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cs4.mm"
include "usgrexmpldifpr.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "prex.mm"
include "s4f1o.mm"
include "mp4an.mm"
include "mp2.mm"
include "f1of1.mm"
include "wf.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "id.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "cn0.mm"
include "cle.mm"
include "0nn0.mm"
include "4nn0.mm"
include "0re.mm"
include "4re.mm"
include "4pos.mm"
include "ltleii.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "eleqtrri.mm"
include "1nn0.mm"
include "1re.mm"
include "1lt4.mm"
include "prelpwi.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "mp2an.mm"
include "fveq2.mm"
include "prhash2ex.mm"
include "syl6eq.mm"
include "jca.mm"
include "2nn0.mm"
include "2re.mm"
include "2lt4.mm"
include "1ne2.mm"
include "cn.mm"
include "wb.mm"
include "1nn.mm"
include "2nn.mm"
include "hashprg.mm"
include "mpbi.mm"
include "jaoi.mm"
include "sylbi.mm"
include "2ne0.mm"
include "cz.mm"
include "2z.mm"
include "0z.mm"
include "3nn0.mm"
include "3re.mm"
include "3lt4.mm"
include "3ne0.mm"
include "necomi.mm"
include "3z.mm"
include "elun.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "anim2i.mm"
include "df-f.mm"
include "anim1i.mm"
include "dff12.mm"
include "mp2b.mm"

theorem usgrexmplef
  let ve: setvar e
  let cE: class E
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vp: setvar p
  assume usgrexmplef.v: |- V = ( 0 ... 4 )
  assume usgrexmplef.e: |- E = <" { 0 , 1 } { 1 , 2 } { 2 , 0 } { 0 , 3 } ">

  disjoint E e
  disjoint V e
  disjoint x y
  disjoint E x
  disjoint E y
  disjoint V x
  disjoint V y
  disjoint p x
  disjoint p y
  disjoint e p
  disjoint V p
  assert |- E : dom E -1-1-> { e e. ~P V | ( # ` e ) = 2 }

  proof
    cE
    cdm
    #
    cc0
    c1
    cpr
    #
    c1
    c2
    cpr
    #
    cpr
    #
    c2
    cc0
    cpr
    #
    cc0
    c3
    cpr
    #
    cpr
    #
    cun
    #
    cE
    wf1o
    #
    @0
    @7
    cE
    wf1
    #
    @0
    ve
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    ve
    cV
    cpw
    #
    crab
    #
    cE
    wf1
    #
    @1
    @2
    wne
    @1
    @4
    wne
    @1
    @5
    wne
    w3a
    @2
    @4
    wne
    @2
    @5
    wne
    @4
    @5
    wne
    w3a
    wa
    #
    cE
    @1
    @2
    @4
    @5
    cs4
    wceq
    #
    @8
    usgrexmpldifpr
    usgrexmplef.e
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @16
    @17
    @8
    wi
    wi
    cc0
    c1
    prex
    c1
    c2
    prex
    c2
    cc0
    prex
    cc0
    c3
    prex
    @1
    @2
    @4
    @5
    cvv
    cE
    s4f1o
    mp4an
    mp2
    @0
    @7
    cE
    f1of1
    @0
    @7
    cE
    wf
    #
    vy
    cv
    vx
    cv
    cE
    wbr
    vy
    wmo
    vx
    wal
    #
    wa
    @0
    @14
    cE
    wf
    #
    @19
    wa
    @9
    @15
    @18
    @20
    @19
    cE
    @0
    wfn
    #
    cE
    crn
    #
    @7
    wss
    #
    wa
    @21
    @22
    @14
    wss
    #
    wa
    @18
    @20
    @23
    @24
    @21
    @23
    @22
    @7
    @14
    @23
    id
    vp
    @7
    @14
    vp
    cv
    #
    @3
    wcel
    #
    @25
    @6
    wcel
    #
    wo
    @25
    @13
    wcel
    #
    @25
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    @25
    @7
    wcel
    @25
    @14
    wcel
    @26
    @31
    @27
    @26
    @25
    @1
    wceq
    #
    @25
    @2
    wceq
    #
    wo
    @31
    @25
    @1
    @2
    vp
    vex
    #
    elpr
    @32
    @31
    @33
    @32
    @28
    @30
    cc0
    cV
    wcel
    #
    c1
    cV
    wcel
    #
    @32
    @28
    wi
    cc0
    cc0
    c4
    cfz
    co
    #
    cV
    cc0
    @37
    wcel
    cc0
    cn0
    wcel
    c4
    cn0
    wcel
    #
    cc0
    c4
    cle
    wbr
    0nn0
    4nn0
    cc0
    c4
    0re
    4re
    4pos
    ltleii
    cc0
    c4
    elfz2nn0
    mpbir3an
    usgrexmplef.v
    eleqtrri
    #
    c1
    @37
    cV
    c1
    @37
    wcel
    c1
    cn0
    wcel
    @38
    c1
    c4
    cle
    wbr
    1nn0
    4nn0
    c1
    c4
    1re
    4re
    1lt4
    ltleii
    c1
    c4
    elfz2nn0
    mpbir3an
    usgrexmplef.v
    eleqtrri
    #
    @35
    @36
    wa
    @28
    @32
    @1
    @13
    wcel
    cc0
    c1
    cV
    prelpwi
    @25
    @1
    @13
    eleq1
    syl5ibrcom
    mp2an
    @32
    @29
    @1
    chash
    cfv
    c2
    @25
    @1
    chash
    fveq2
    prhash2ex
    syl6eq
    jca
    @33
    @28
    @30
    @36
    c2
    cV
    wcel
    #
    @33
    @28
    wi
    @40
    c2
    @37
    cV
    c2
    @37
    wcel
    c2
    cn0
    wcel
    @38
    c2
    c4
    cle
    wbr
    2nn0
    4nn0
    c2
    c4
    2re
    4re
    2lt4
    ltleii
    c2
    c4
    elfz2nn0
    mpbir3an
    usgrexmplef.v
    eleqtrri
    #
    @36
    @41
    wa
    @28
    @33
    @2
    @13
    wcel
    c1
    c2
    cV
    prelpwi
    @25
    @2
    @13
    eleq1
    syl5ibrcom
    mp2an
    @33
    @29
    @2
    chash
    cfv
    #
    c2
    @25
    @2
    chash
    fveq2
    c1
    c2
    wne
    #
    @43
    c2
    wceq
    #
    1ne2
    c1
    cn
    wcel
    c2
    cn
    wcel
    @44
    @45
    wb
    1nn
    2nn
    c1
    c2
    cn
    cn
    hashprg
    mp2an
    mpbi
    syl6eq
    jca
    jaoi
    sylbi
    @27
    @25
    @4
    wceq
    #
    @25
    @5
    wceq
    #
    wo
    @31
    @25
    @4
    @5
    @34
    elpr
    @46
    @31
    @47
    @46
    @28
    @30
    @41
    @35
    @46
    @28
    wi
    @42
    @39
    @41
    @35
    wa
    @28
    @46
    @4
    @13
    wcel
    c2
    cc0
    cV
    prelpwi
    @25
    @4
    @13
    eleq1
    syl5ibrcom
    mp2an
    @46
    @29
    @4
    chash
    cfv
    #
    c2
    @25
    @4
    chash
    fveq2
    c2
    cc0
    wne
    #
    @48
    c2
    wceq
    #
    2ne0
    c2
    cz
    wcel
    cc0
    cz
    wcel
    #
    @49
    @50
    wb
    2z
    0z
    c2
    cc0
    cz
    cz
    hashprg
    mp2an
    mpbi
    syl6eq
    jca
    @47
    @28
    @30
    @35
    c3
    cV
    wcel
    #
    @47
    @28
    wi
    @39
    c3
    @37
    cV
    c3
    @37
    wcel
    c3
    cn0
    wcel
    @38
    c3
    c4
    cle
    wbr
    3nn0
    4nn0
    c3
    c4
    3re
    4re
    3lt4
    ltleii
    c3
    c4
    elfz2nn0
    mpbir3an
    usgrexmplef.v
    eleqtrri
    @35
    @52
    wa
    @28
    @47
    @5
    @13
    wcel
    cc0
    c3
    cV
    prelpwi
    @25
    @5
    @13
    eleq1
    syl5ibrcom
    mp2an
    @47
    @29
    @5
    chash
    cfv
    #
    c2
    @25
    @5
    chash
    fveq2
    cc0
    c3
    wne
    #
    @53
    c2
    wceq
    #
    c3
    cc0
    3ne0
    necomi
    @51
    c3
    cz
    wcel
    @54
    @55
    wb
    0z
    3z
    cc0
    c3
    cz
    cz
    hashprg
    mp2an
    mpbi
    syl6eq
    jca
    jaoi
    sylbi
    jaoi
    @25
    @3
    @6
    elun
    @12
    @30
    ve
    @25
    @13
    @10
    @25
    wceq
    @11
    @29
    c2
    @10
    @25
    chash
    fveq2
    eqeq1d
    elrab
    3imtr4i
    ssriv
    syl6ss
    anim2i
    @0
    @7
    cE
    df-f
    @0
    @14
    cE
    df-f
    3imtr4i
    anim1i
    vy
    vx
    @0
    @7
    cE
    dff12
    vy
    vx
    @0
    @14
    cE
    dff12
    3imtr4i
    mp2b
end
