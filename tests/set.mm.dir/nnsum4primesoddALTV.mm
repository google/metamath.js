include "c8.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "c7.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbo.mm"
include "wi.mm"
include "wral.mm"
include "c1.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "cprime.mm"
include "cmap.mm"
include "wrex.mm"
include "breq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "adantl.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "eluz2.mm"
include "7lt8.mm"
include "cr.mm"
include "7re.mm"
include "a1i.mm"
include "8re.mm"
include "zre.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "adantr.mm"
include "pm2.27.mm"
include "syl.mm"
include "caddc.mm"
include "isgbo.mm"
include "cop.mm"
include "c2.mm"
include "ctp.mm"
include "wf.mm"
include "1ex.mm"
include "2ex.mm"
include "3ex.mm"
include "vex.mm"
include "1ne2.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "2re.mm"
include "2lt3.mm"
include "ftp.mm"
include "1p2e3.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "1z.mm"
include "fztp.mm"
include "ax-mp.mm"
include "eqid.mm"
include "id.mm"
include "1p1e2.mm"
include "tpeq123d.mm"
include "3eqtri.mm"
include "feq2i.mm"
include "sylibr.mm"
include "wss.mm"
include "df-3an.mm"
include "tpss.mm"
include "sylbb1.mm"
include "fssd.mm"
include "cvv.mm"
include "wb.mm"
include "prmex.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "fveq1.mm"
include "sumeq2sdv.mm"
include "eqeq2d.mm"
include "sumeq1d.mm"
include "fveq2.mm"
include "wne.mm"
include "fvtp1.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "fvtp2.mm"
include "fvtp3.mm"
include "cc.mm"
include "prmz.mm"
include "zcnd.mm"
include "3anim123i.mm"
include "3expa.mm"
include "2z.mm"
include "3z.mm"
include "3pm3.2i.mm"
include "sumtp.mm"
include "eqtr2d.mm"
include "rspcedvd.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "rexlimivv.mm"
include "3syld.mm"
include "com12.mm"

theorem nnsum4primesoddALTV
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vx: setvar x

  disjoint N f
  disjoint N k
  disjoint N m
  disjoint f k
  disjoint f m
  disjoint k m
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) -> ( ( N e. ( ZZ>= ` 8 ) /\ N e. Odd ) -> E. f e. ( Prime ^m ( 1 ... 3 ) ) N = sum_ k e. ( 1 ... 3 ) ( f ` k ) ) )

  proof
    cN
    c8
    cuz
    cfv
    wcel
    #
    cN
    codd
    wcel
    #
    wa
    #
    c7
    vm
    cv
    #
    clt
    wbr
    #
    @3
    cgbo
    wcel
    #
    wi
    #
    vm
    codd
    wral
    #
    cN
    c1
    c3
    cfz
    co
    #
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vf
    cprime
    @8
    cmap
    co
    #
    wrex
    #
    @2
    @7
    c7
    cN
    clt
    wbr
    #
    cN
    cgbo
    wcel
    #
    wi
    #
    @17
    @15
    @1
    @7
    @18
    wi
    @0
    @6
    @18
    vm
    cN
    codd
    @3
    cN
    wceq
    @4
    @16
    @5
    @17
    @3
    cN
    c7
    clt
    breq2
    @3
    cN
    cgbo
    eleq1
    imbi12d
    rspcv
    adantl
    @2
    @16
    @18
    @17
    wi
    @0
    @16
    @1
    @0
    c8
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c8
    cN
    cle
    wbr
    #
    w3a
    @16
    c8
    cN
    eluz2
    @20
    @21
    @16
    @19
    @20
    @21
    @16
    @20
    c7
    c8
    clt
    wbr
    #
    @21
    @16
    7lt8
    @20
    c7
    cr
    wcel
    #
    c8
    cr
    wcel
    #
    cN
    cr
    wcel
    @22
    @21
    wa
    @16
    wi
    @23
    @20
    7re
    a1i
    @24
    @20
    8re
    a1i
    cN
    zre
    c7
    c8
    cN
    ltletr
    syl3anc
    mpani
    imp
    3adant1
    sylbi
    adantr
    @16
    @17
    pm2.27
    syl
    @17
    @15
    wi
    @2
    @17
    @1
    vp
    cv
    #
    codd
    wcel
    vq
    cv
    #
    codd
    wcel
    vr
    cv
    #
    codd
    wcel
    w3a
    #
    cN
    @25
    @26
    caddc
    co
    @27
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    wa
    @15
    cN
    vr
    vq
    vp
    isgbo
    @33
    @15
    @1
    @32
    @15
    vp
    vq
    cprime
    cprime
    @25
    cprime
    wcel
    #
    @26
    cprime
    wcel
    #
    wa
    #
    @31
    @15
    vr
    cprime
    @36
    @27
    cprime
    wcel
    #
    wa
    #
    @30
    @15
    @28
    @38
    @15
    @30
    @29
    @12
    wceq
    #
    vf
    @14
    wrex
    @38
    @39
    @29
    @8
    @9
    c1
    @25
    cop
    c2
    @26
    cop
    c3
    @27
    cop
    ctp
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vf
    @40
    @14
    @38
    @40
    @14
    wcel
    #
    @8
    cprime
    @40
    wf
    #
    @38
    @8
    @25
    @26
    @27
    ctp
    #
    cprime
    @40
    @38
    c1
    c2
    c3
    ctp
    #
    @46
    @40
    wf
    #
    @8
    @46
    @40
    wf
    @48
    @38
    c1
    c2
    c3
    @25
    @26
    @27
    1ex
    2ex
    3ex
    vp
    vex
    #
    vq
    vex
    #
    vr
    vex
    #
    1ne2
    c1
    c3
    1re
    1lt3
    ltneii
    #
    c2
    c3
    2re
    2lt3
    ltneii
    #
    ftp
    a1i
    @8
    @47
    @46
    @40
    @8
    c1
    c1
    c2
    caddc
    co
    #
    cfz
    co
    #
    c1
    c1
    c1
    caddc
    co
    #
    @54
    ctp
    #
    @47
    c3
    @54
    c1
    cfz
    @54
    c3
    1p2e3
    eqcomi
    oveq2i
    c1
    cz
    wcel
    #
    @55
    @57
    wceq
    1z
    c1
    fztp
    ax-mp
    c1
    c1
    wceq
    #
    @57
    @47
    wceq
    c1
    eqid
    @59
    c1
    c1
    @56
    c2
    @54
    c3
    @59
    id
    @56
    c2
    wceq
    @59
    1p1e2
    a1i
    @54
    c3
    wceq
    @59
    1p2e3
    a1i
    tpeq123d
    ax-mp
    3eqtri
    #
    feq2i
    sylibr
    @34
    @35
    @37
    w3a
    @38
    @46
    cprime
    wss
    @34
    @35
    @37
    df-3an
    @25
    @26
    @27
    cprime
    @49
    @50
    @51
    tpss
    sylbb1
    fssd
    cprime
    cvv
    wcel
    #
    @8
    cvv
    wcel
    #
    wa
    @44
    @45
    wb
    @38
    @61
    @62
    prmex
    c1
    c3
    cfz
    ovex
    pm3.2i
    cprime
    @8
    @40
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    @10
    @40
    wceq
    #
    @39
    @43
    wb
    @38
    @63
    @12
    @42
    @29
    @63
    @8
    @11
    @41
    vk
    @9
    @10
    @40
    fveq1
    sumeq2sdv
    eqeq2d
    adantl
    @38
    @42
    @47
    @41
    vk
    csu
    @29
    @38
    @8
    @47
    @41
    vk
    @8
    @47
    wceq
    @38
    @60
    a1i
    sumeq1d
    @38
    c1
    c2
    c3
    @41
    vk
    @25
    @26
    @27
    cz
    cz
    cz
    @9
    c1
    wceq
    @41
    c1
    @40
    cfv
    #
    @25
    @9
    c1
    @40
    fveq2
    c1
    c2
    wne
    #
    c1
    c3
    wne
    #
    @64
    @25
    wceq
    1ne2
    @52
    c1
    c2
    c3
    @25
    @26
    @27
    1ex
    @49
    fvtp1
    mp2an
    syl6eq
    @9
    c2
    wceq
    @41
    c2
    @40
    cfv
    #
    @26
    @9
    c2
    @40
    fveq2
    @65
    c2
    c3
    wne
    #
    @67
    @26
    wceq
    1ne2
    @53
    c1
    c2
    c3
    @25
    @26
    @27
    2ex
    @50
    fvtp2
    mp2an
    syl6eq
    @9
    c3
    wceq
    @41
    c3
    @40
    cfv
    #
    @27
    @9
    c3
    @40
    fveq2
    @66
    @68
    @69
    @27
    wceq
    @52
    @53
    c1
    c2
    c3
    @25
    @26
    @27
    3ex
    @51
    fvtp3
    mp2an
    syl6eq
    @34
    @35
    @37
    @25
    cc
    wcel
    #
    @26
    cc
    wcel
    #
    @27
    cc
    wcel
    #
    w3a
    @34
    @70
    @35
    @71
    @37
    @72
    @34
    @25
    @25
    prmz
    zcnd
    @35
    @26
    @26
    prmz
    zcnd
    @37
    @27
    @27
    prmz
    zcnd
    3anim123i
    3expa
    @58
    c2
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    w3a
    @38
    @58
    @73
    @74
    1z
    2z
    3z
    3pm3.2i
    a1i
    @65
    @38
    1ne2
    a1i
    @66
    @38
    @52
    a1i
    @68
    @38
    @53
    a1i
    sumtp
    eqtr2d
    rspcedvd
    @30
    @13
    @39
    vf
    @14
    cN
    @29
    @12
    eqeq1
    rexbidv
    syl5ibrcom
    adantld
    rexlimdva
    rexlimivv
    adantl
    sylbi
    a1i
    3syld
    com12
end
