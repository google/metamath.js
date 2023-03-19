include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "wcel.mm"
include "wal.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "breq1.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "cz.mm"
include "ssel.mm"
include "eluzle.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "adantr.mm"
include "a1i.mm"
include "uzssz.mm"
include "sstr.mm"
include "mpan2.mm"
include "eluzelz.mm"
include "rspcev.mm"
include "expcom.mm"
include "con3rr3.mm"
include "wb.mm"
include "ssel2.mm"
include "cr.mm"
include "zre.mm"
include "letri3.mm"
include "syl2an.mm"
include "clt.mm"
include "zleltp1.mm"
include "peano2re.mm"
include "syl.mm"
include "ltnle.mm"
include "bitrd.mm"
include "ancoms.mm"
include "anbi2d.mm"
include "sylan2.mm"
include "eleq1a.mm"
include "ad2antll.mm"
include "sylbird.mm"
include "expd.mm"
include "con1.mm"
include "com23.mm"
include "exp32.mm"
include "com34.mm"
include "imp41.mm"
include "ralimdva.mm"
include "ex.mm"
include "sylan9r.mm"
include "pm2.43d.mm"
include "expl.mm"
include "sylani.mm"
include "a2d.mm"
include "uzind4.mm"
include "adantl.mm"
include "sylcom.mm"
include "adantrd.mm"
include "pm2.61i.mm"
include "alrimdv.mm"
include "eq0.mm"
include "syl6ibr.mm"
include "necon1ad.mm"
include "imp.mm"
include "breq2.mm"
include "cbvralv.mm"
include "rexbii.mm"
include "sylib.mm"

theorem uzwo
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let vh: setvar h
  let vt: setvar t
  let vn: setvar n
  let vm: setvar m

  disjoint j k
  disjoint S j
  disjoint S k
  disjoint h t
  disjoint h n
  disjoint h m
  disjoint M h
  disjoint n t
  disjoint m t
  disjoint M t
  disjoint m n
  disjoint M n
  disjoint M m
  disjoint h j
  disjoint h k
  disjoint S h
  disjoint j t
  disjoint j m
  disjoint j n
  disjoint k t
  disjoint S t
  disjoint k m
  disjoint k n
  disjoint S m
  disjoint S n
  assert |- ( ( S C_ ( ZZ>= ` M ) /\ S =/= (/) ) -> E. j e. S A. k e. S j <_ k )

  proof
    cS
    cM
    cuz
    cfv
    #
    wss
    #
    cS
    c0
    wne
    #
    wa
    vj
    cv
    #
    vt
    cv
    #
    cle
    wbr
    #
    vt
    cS
    wral
    #
    vj
    cS
    wrex
    #
    @3
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cS
    wral
    #
    vj
    cS
    wrex
    @1
    @2
    @7
    @1
    @7
    cS
    c0
    @1
    @7
    wn
    #
    vn
    cv
    #
    cS
    wcel
    #
    wn
    #
    vn
    wal
    cS
    c0
    wceq
    @1
    @11
    @14
    vn
    @1
    @11
    @14
    @12
    @0
    wcel
    #
    @1
    @11
    wa
    #
    @14
    wi
    @15
    @16
    @12
    @4
    cle
    wbr
    #
    vt
    cS
    wral
    #
    @14
    @16
    vh
    cv
    #
    @4
    cle
    wbr
    #
    vt
    cS
    wral
    #
    wi
    @16
    cM
    @4
    cle
    wbr
    #
    vt
    cS
    wral
    #
    wi
    #
    @16
    vm
    cv
    #
    @4
    cle
    wbr
    #
    vt
    cS
    wral
    #
    wi
    @16
    @25
    c1
    caddc
    co
    #
    @4
    cle
    wbr
    #
    vt
    cS
    wral
    #
    wi
    @16
    @18
    wi
    vh
    vm
    cM
    @12
    @19
    cM
    wceq
    #
    @21
    @23
    @16
    @31
    @20
    @22
    vt
    cS
    @19
    cM
    @4
    cle
    breq1
    ralbidv
    imbi2d
    @19
    @25
    wceq
    #
    @21
    @27
    @16
    @32
    @20
    @26
    vt
    cS
    @19
    @25
    @4
    cle
    breq1
    ralbidv
    imbi2d
    @19
    @28
    wceq
    #
    @21
    @30
    @16
    @33
    @20
    @29
    vt
    cS
    @19
    @28
    @4
    cle
    breq1
    ralbidv
    imbi2d
    @19
    @12
    wceq
    #
    @21
    @18
    @16
    @34
    @20
    @17
    vt
    cS
    @19
    @12
    @4
    cle
    breq1
    ralbidv
    imbi2d
    @24
    cM
    cz
    wcel
    @1
    @23
    @11
    @1
    @22
    vt
    cS
    @1
    @4
    cS
    wcel
    #
    @4
    @0
    wcel
    @22
    cS
    @0
    @4
    ssel
    cM
    @4
    eluzle
    syl6
    ralrimiv
    adantr
    a1i
    @25
    @0
    wcel
    #
    @16
    @27
    @30
    @1
    @36
    cS
    cz
    wss
    #
    @11
    @27
    @30
    wi
    #
    @1
    @0
    cz
    wss
    @37
    cM
    uzssz
    cS
    @0
    cz
    sstr
    mpan2
    @36
    @25
    cz
    wcel
    #
    @37
    @11
    wa
    @38
    wi
    cM
    @25
    eluzelz
    @39
    @37
    @11
    @38
    @39
    @37
    wa
    #
    @11
    wa
    @27
    @30
    @11
    @27
    @25
    cS
    wcel
    #
    wn
    #
    @40
    @38
    @27
    @41
    @7
    @41
    @27
    @7
    @6
    @27
    vj
    @25
    cS
    @3
    @25
    wceq
    @5
    @26
    vt
    cS
    @3
    @25
    @4
    cle
    breq1
    ralbidv
    rspcev
    expcom
    con3rr3
    @40
    @42
    @38
    @40
    @42
    wa
    @26
    @29
    vt
    cS
    @39
    @37
    @42
    @35
    @26
    @29
    wi
    #
    @39
    @37
    @35
    @42
    @43
    @39
    @37
    @35
    @42
    @43
    wi
    @39
    @37
    @35
    wa
    #
    wa
    #
    @26
    @42
    @29
    @45
    @26
    @29
    wn
    #
    @41
    wi
    @42
    @29
    wi
    @45
    @26
    @46
    @41
    @45
    @26
    @46
    wa
    #
    @25
    @4
    wceq
    #
    @41
    @44
    @39
    @4
    cz
    wcel
    #
    @48
    @47
    wb
    cS
    cz
    @4
    ssel2
    @39
    @49
    wa
    #
    @48
    @26
    @4
    @25
    cle
    wbr
    #
    wa
    #
    @47
    @39
    @25
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @48
    @52
    wb
    @49
    @25
    zre
    #
    @4
    zre
    #
    @25
    @4
    letri3
    syl2an
    @50
    @51
    @46
    @26
    @49
    @39
    @51
    @46
    wb
    @49
    @39
    wa
    @51
    @4
    @28
    clt
    wbr
    #
    @46
    @4
    @25
    zleltp1
    @49
    @54
    @28
    cr
    wcel
    #
    @57
    @46
    wb
    @39
    @56
    @39
    @53
    @58
    @55
    @25
    peano2re
    syl
    @4
    @28
    ltnle
    syl2an
    bitrd
    ancoms
    anbi2d
    bitrd
    sylan2
    @35
    @48
    @41
    wi
    @39
    @37
    @4
    cS
    @25
    eleq1a
    ad2antll
    sylbird
    expd
    @29
    @41
    con1
    syl6
    com23
    exp32
    com34
    imp41
    ralimdva
    ex
    sylan9r
    pm2.43d
    expl
    syl
    sylani
    a2d
    uzind4
    @11
    @18
    @14
    wi
    @1
    @18
    @13
    @7
    @13
    @18
    @7
    @6
    @18
    vj
    @12
    cS
    @3
    @12
    wceq
    @5
    @17
    vt
    cS
    @3
    @12
    @4
    cle
    breq1
    ralbidv
    rspcev
    expcom
    con3rr3
    adantl
    sylcom
    @15
    wn
    @1
    @14
    @11
    @1
    @13
    @15
    cS
    @0
    @12
    ssel
    con3rr3
    adantrd
    pm2.61i
    ex
    alrimdv
    vn
    cS
    eq0
    syl6ibr
    necon1ad
    imp
    @6
    @10
    vj
    cS
    @5
    @9
    vt
    vk
    cS
    @4
    @8
    @3
    cle
    breq2
    cbvralv
    rexbii
    sylib
end
