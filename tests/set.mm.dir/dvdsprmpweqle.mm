include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "dvdsprmpweq.mm"
include "imp.mm"
include "clt.mm"
include "wo.mm"
include "cr.mm"
include "nn0re.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "anim12i.mm"
include "ancomd.mm"
include "lelttric.mm"
include "syl.mm"
include "wi.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "cdiv.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "3ad2ant1.mm"
include "simpr.mm"
include "nn0expcld.mm"
include "nn0zd.mm"
include "cc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "nn0z.mm"
include "expne0d.mm"
include "simp3.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "cmin.mm"
include "jca.mm"
include "expsub.mm"
include "eqcomd.mm"
include "syl2an2r.mm"
include "eleq1d.mm"
include "c1.mm"
include "cneg.mm"
include "nn0cn.mm"
include "subcld.mm"
include "negsubdi2.mm"
include "anim1i.mm"
include "ltsubnn0.mm"
include "eqeltrd.mm"
include "expneg2.mm"
include "wn.mm"
include "nnred.mm"
include "reexpcld.mm"
include "znnsub.mm"
include "biimpa.mm"
include "prmgt1.mm"
include "expgt1.mm"
include "oveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "recnz.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "imp41.mm"
include "com12.mm"
include "jao1i.mm"
include "mpcom.mm"
include "reximdva.mm"

theorem dvdsprmpweqle
  let cA: class A
  let cP: class P
  let vn: setvar n
  let cN: class N

  disjoint A n
  disjoint N n
  disjoint P n
  assert |- ( ( P e. Prime /\ A e. NN /\ N e. NN0 ) -> ( A || ( P ^ N ) -> E. n e. NN0 ( n <_ N /\ A = ( P ^ n ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cn
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cP
    cN
    cexp
    co
    #
    cdvds
    wbr
    #
    vn
    cv
    #
    cN
    cle
    wbr
    #
    cA
    cP
    @6
    cexp
    co
    #
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    #
    @3
    @5
    wa
    #
    @9
    vn
    cn0
    wrex
    #
    @11
    @3
    @5
    @13
    cA
    cP
    vn
    cN
    dvdsprmpweq
    imp
    @12
    @9
    @10
    vn
    cn0
    @12
    @6
    cn0
    wcel
    #
    wa
    #
    @9
    @10
    @15
    @9
    wa
    #
    @7
    @9
    @7
    cN
    @6
    clt
    wbr
    #
    wo
    #
    @16
    @7
    @16
    @6
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    wa
    #
    @18
    @15
    @21
    @9
    @15
    @20
    @19
    @12
    @20
    @14
    @19
    @3
    @20
    @5
    @2
    @0
    @20
    @1
    cN
    nn0re
    3ad2ant3
    adantr
    @6
    nn0re
    anim12i
    ancomd
    adantr
    @6
    cN
    lelttric
    syl
    @7
    @17
    @16
    @16
    @17
    @7
    @3
    @5
    @14
    @9
    @17
    @7
    wi
    #
    @3
    @14
    @5
    @9
    @22
    wi
    #
    @3
    @14
    @5
    @23
    wi
    @3
    @14
    wa
    #
    @9
    @5
    @22
    @24
    @9
    @5
    @22
    wi
    @24
    @9
    wa
    @5
    @8
    @4
    cdvds
    wbr
    #
    @22
    @9
    @5
    @25
    wb
    @24
    cA
    @8
    @4
    cdvds
    breq1
    adantl
    @24
    @25
    @22
    wi
    @9
    @24
    @25
    @4
    @8
    cdiv
    co
    #
    cz
    wcel
    #
    @22
    @24
    @8
    cz
    wcel
    @8
    cc0
    wne
    @4
    cz
    wcel
    @25
    @27
    wb
    @24
    @8
    @24
    cP
    @6
    @3
    cP
    cn0
    wcel
    #
    @14
    @0
    @1
    @28
    @2
    @0
    cP
    cP
    prmnn
    #
    nnnn0d
    3ad2ant1
    adantr
    #
    @3
    @14
    simpr
    nn0expcld
    nn0zd
    @24
    cP
    @6
    @3
    cP
    cc
    wcel
    #
    @14
    @0
    @1
    @31
    @2
    @0
    cP
    @29
    nncnd
    #
    3ad2ant1
    adantr
    #
    @3
    cP
    cc0
    wne
    #
    @14
    @0
    @1
    @34
    @2
    @0
    cP
    @29
    nnne0d
    #
    3ad2ant1
    adantr
    @14
    @6
    cz
    wcel
    #
    @3
    @6
    nn0z
    #
    adantl
    expne0d
    @24
    @4
    @24
    cP
    cN
    @30
    @3
    @2
    @14
    @0
    @1
    @2
    simp3
    #
    adantr
    nn0expcld
    nn0zd
    @8
    @4
    dvdsval2
    syl3anc
    @24
    @27
    cP
    cN
    @6
    cmin
    co
    #
    cexp
    co
    #
    cz
    wcel
    #
    @22
    @24
    @26
    @40
    cz
    @3
    @31
    @34
    wa
    #
    @14
    cN
    cz
    wcel
    #
    @36
    wa
    #
    @26
    @40
    wceq
    @0
    @1
    @42
    @2
    @0
    @31
    @34
    @32
    @35
    jca
    3ad2ant1
    @3
    @43
    @14
    @36
    @2
    @0
    @43
    @1
    cN
    nn0z
    3ad2ant3
    @37
    anim12i
    #
    @42
    @44
    wa
    @40
    @26
    cP
    cN
    @6
    expsub
    eqcomd
    syl2an2r
    eleq1d
    @24
    @17
    @41
    @7
    @24
    @17
    @41
    @7
    wi
    @24
    @17
    wa
    #
    @41
    c1
    cP
    @39
    cneg
    #
    cexp
    co
    #
    cdiv
    co
    #
    cz
    wcel
    #
    @7
    @46
    @40
    @49
    cz
    @46
    @31
    @39
    cc
    wcel
    #
    @47
    cn0
    wcel
    @40
    @49
    wceq
    @24
    @31
    @17
    @33
    adantr
    @24
    @51
    @17
    @24
    cN
    @6
    @3
    cN
    cc
    wcel
    #
    @14
    @2
    @0
    @52
    @1
    cN
    nn0cn
    3ad2ant3
    #
    adantr
    @14
    @6
    cc
    wcel
    #
    @3
    @6
    nn0cn
    #
    adantl
    subcld
    adantr
    @46
    @47
    @6
    cN
    cmin
    co
    #
    cn0
    @46
    @52
    @54
    wa
    #
    @47
    @56
    wceq
    #
    @24
    @57
    @17
    @3
    @52
    @14
    @54
    @53
    @55
    anim12i
    adantr
    cN
    @6
    negsubdi2
    syl
    #
    @24
    @17
    @56
    cn0
    wcel
    #
    @24
    @14
    @2
    wa
    @17
    @60
    wi
    @24
    @2
    @14
    @3
    @2
    @14
    @38
    anim1i
    ancomd
    @6
    cN
    ltsubnn0
    syl
    imp
    #
    eqeltrd
    cP
    @39
    expneg2
    syl3anc
    eleq1d
    @46
    @50
    @7
    @46
    @48
    cr
    wcel
    #
    c1
    @48
    clt
    wbr
    #
    wa
    #
    @50
    wn
    @46
    @58
    @64
    @59
    @46
    @64
    @58
    cP
    @56
    cexp
    co
    #
    cr
    wcel
    #
    c1
    @65
    clt
    wbr
    #
    wa
    @46
    @66
    @67
    @46
    cP
    @56
    @24
    cP
    cr
    wcel
    #
    @17
    @3
    @68
    @14
    @0
    @1
    @68
    @2
    @0
    cP
    @29
    nnred
    3ad2ant1
    adantr
    adantr
    #
    @61
    reexpcld
    @46
    @68
    @56
    cn
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @67
    @69
    @24
    @17
    @70
    @24
    @44
    @17
    @70
    wb
    @45
    cN
    @6
    znnsub
    syl
    biimpa
    @24
    @71
    @17
    @3
    @71
    @14
    @0
    @1
    @71
    @2
    cP
    prmgt1
    3ad2ant1
    adantr
    adantr
    cP
    @56
    expgt1
    syl3anc
    jca
    @58
    @62
    @66
    @63
    @67
    @58
    @48
    @65
    cr
    @47
    @56
    cP
    cexp
    oveq2
    #
    eleq1d
    @58
    @48
    @65
    c1
    clt
    @72
    breq2d
    anbi12d
    syl5ibrcom
    mpd
    @48
    recnz
    syl
    pm2.21d
    sylbid
    ex
    com23
    sylbid
    sylbid
    adantr
    sylbid
    ex
    com23
    ex
    com23
    imp41
    com12
    jao1i
    mpcom
    @15
    @9
    simpr
    jca
    ex
    reximdva
    mpd
    ex
end
