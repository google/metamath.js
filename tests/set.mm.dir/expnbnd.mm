include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cn.mm"
include "wrex.mm"
include "wa.mm"
include "1nn.mm"
include "wi.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an2.mm"
include "exp4b.mm"
include "com34.mm"
include "3imp1.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "exp1.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "cle.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "caddc.mm"
include "cn0.mm"
include "cc0.mm"
include "peano2rem.mm"
include "adantl.mm"
include "wne.mm"
include "wb.mm"
include "posdif.mm"
include "mpan.mm"
include "biimpa.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "adantll.mm"
include "subge0.mm"
include "mpan2.mm"
include "biimparc.mm"
include "jca.mm"
include "divge0.mm"
include "syl2an.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0p1nn.mm"
include "cmul.mm"
include "simplr.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "remulcld.mm"
include "peano2re.mm"
include "simprl.mm"
include "reexpcl.mm"
include "flltp1.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltsubadd.mm"
include "0lt1.mm"
include "0re.mm"
include "mp3an12.mm"
include "mpani.mm"
include "ltle.mm"
include "syld.mm"
include "imp.mm"
include "bernneq2.mm"
include "syl3anc.mm"
include "ltletrd.mm"
include "exp43.mm"
include "com4l.mm"
include "simp1.mm"
include "1red.mm"
include "ltlecasei.mm"

theorem expnbnd
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vj: setvar j

  disjoint A k
  disjoint B k
  disjoint j k
  disjoint A j
  disjoint B j
  assert |- ( ( A e. RR /\ B e. RR /\ 1 < B ) -> E. k e. NN A < ( B ^ k ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    w3a
    #
    cA
    cB
    vk
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    cA
    c1
    @3
    cA
    c1
    clt
    wbr
    #
    wa
    #
    c1
    cn
    wcel
    cA
    cB
    c1
    cexp
    co
    #
    clt
    wbr
    #
    @7
    1nn
    @9
    cA
    cB
    @10
    clt
    @0
    @1
    @2
    @8
    cA
    cB
    clt
    wbr
    #
    @0
    @1
    @8
    @2
    @12
    @0
    @1
    @8
    @2
    @12
    @0
    c1
    cr
    wcel
    #
    @1
    @8
    @2
    wa
    @12
    wi
    1re
    cA
    c1
    cB
    lttr
    mp3an2
    exp4b
    com34
    3imp1
    @3
    @10
    cB
    wceq
    #
    @8
    @1
    @0
    @14
    @2
    @1
    cB
    cc
    wcel
    @14
    cB
    recn
    cB
    exp1
    syl
    3ad2ant2
    adantr
    breqtrrd
    @6
    @11
    vk
    c1
    cn
    @4
    c1
    wceq
    @5
    @10
    cA
    clt
    @4
    c1
    cB
    cexp
    oveq2
    breq2d
    rspcev
    sylancr
    @0
    @1
    @2
    c1
    cA
    cle
    wbr
    #
    @7
    @15
    @0
    @1
    @2
    @7
    @15
    @0
    @1
    @2
    @7
    @15
    @0
    wa
    #
    @1
    @2
    wa
    #
    wa
    #
    cA
    c1
    cmin
    co
    #
    cB
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    cA
    cB
    @23
    cexp
    co
    #
    clt
    wbr
    #
    @7
    @18
    @22
    cn0
    wcel
    #
    @24
    @18
    @21
    cr
    wcel
    #
    cc0
    @21
    cle
    wbr
    #
    @27
    @0
    @17
    @28
    @15
    @0
    @17
    wa
    @19
    @20
    @0
    @19
    cr
    wcel
    #
    @17
    cA
    peano2rem
    #
    adantr
    @17
    @20
    cr
    wcel
    #
    @0
    @1
    @32
    @2
    cB
    peano2rem
    adantr
    #
    adantl
    @17
    @20
    cc0
    wne
    @0
    @17
    @20
    @1
    @2
    cc0
    @20
    clt
    wbr
    #
    @13
    @1
    @2
    @34
    wb
    1re
    c1
    cB
    posdif
    mpan
    biimpa
    #
    gt0ne0d
    adantl
    redivcld
    adantll
    #
    @16
    @30
    cc0
    @19
    cle
    wbr
    #
    wa
    @32
    @34
    wa
    @29
    @17
    @16
    @30
    @37
    @0
    @30
    @15
    @31
    adantl
    #
    @0
    @37
    @15
    @0
    @13
    @37
    @15
    wb
    1re
    cA
    c1
    subge0
    mpan2
    biimparc
    jca
    @17
    @32
    @34
    @33
    @35
    jca
    @19
    @20
    divge0
    syl2an
    @21
    flge0nn0
    syl2anc
    #
    @22
    nn0p1nn
    syl
    @18
    cA
    @20
    @23
    cmul
    co
    #
    c1
    caddc
    co
    #
    @25
    @15
    @0
    @17
    simplr
    #
    @18
    @40
    cr
    wcel
    #
    @41
    cr
    wcel
    @18
    @20
    @23
    @17
    @32
    @16
    @33
    adantl
    #
    @18
    @23
    @18
    @27
    @23
    cn0
    wcel
    #
    @39
    @22
    peano2nn0
    syl
    #
    nn0red
    #
    remulcld
    #
    @40
    peano2re
    syl
    @18
    @1
    @45
    @25
    cr
    wcel
    @16
    @1
    @2
    simprl
    #
    @46
    cB
    @23
    reexpcl
    syl2anc
    @18
    @19
    @40
    clt
    wbr
    #
    cA
    @41
    clt
    wbr
    #
    @18
    @21
    @23
    clt
    wbr
    #
    @50
    @18
    @28
    @52
    @36
    @21
    flltp1
    syl
    @18
    @30
    @23
    cr
    wcel
    @32
    @34
    @52
    @50
    wb
    @16
    @30
    @17
    @38
    adantr
    @47
    @44
    @17
    @34
    @16
    @35
    adantl
    @19
    @23
    @20
    ltdivmul
    syl112anc
    mpbid
    @18
    @0
    @43
    @50
    @51
    wb
    #
    @42
    @48
    @0
    @13
    @43
    @53
    1re
    cA
    c1
    @40
    ltsubadd
    mp3an2
    syl2anc
    mpbid
    @18
    @1
    @45
    cc0
    cB
    cle
    wbr
    #
    @41
    @25
    cle
    wbr
    @49
    @46
    @17
    @54
    @16
    @1
    @2
    @54
    @1
    @2
    cc0
    cB
    clt
    wbr
    #
    @54
    @1
    cc0
    c1
    clt
    wbr
    #
    @2
    @55
    0lt1
    cc0
    cr
    wcel
    #
    @13
    @1
    @56
    @2
    wa
    @55
    wi
    0re
    1re
    cc0
    c1
    cB
    lttr
    mp3an12
    mpani
    @57
    @1
    @55
    @54
    wi
    0re
    cc0
    cB
    ltle
    mpan
    syld
    imp
    adantl
    cB
    @23
    bernneq2
    syl3anc
    ltletrd
    @6
    @26
    vk
    @23
    cn
    @4
    @23
    wceq
    @5
    @25
    cA
    clt
    @4
    @23
    cB
    cexp
    oveq2
    breq2d
    rspcev
    syl2anc
    exp43
    com4l
    3imp1
    @0
    @1
    @2
    simp1
    @3
    1red
    ltlecasei
end
