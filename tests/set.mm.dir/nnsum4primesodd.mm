include "c6.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "c5.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbow.mm"
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
include "5lt6.mm"
include "cr.mm"
include "5re.mm"
include "a1i.mm"
include "6re.mm"
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
include "isgbow.mm"
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
include "rexlimdva.mm"
include "rexlimivv.mm"
include "3syld.mm"
include "com12.mm"

theorem nnsum4primesodd
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
  assert |- ( A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) -> ( ( N e. ( ZZ>= ` 6 ) /\ N e. Odd ) -> E. f e. ( Prime ^m ( 1 ... 3 ) ) N = sum_ k e. ( 1 ... 3 ) ( f ` k ) ) )

  proof
    cN
    c6
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
    c5
    vm
    cv
    #
    clt
    wbr
    #
    @3
    cgbow
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
    c5
    cN
    clt
    wbr
    #
    cN
    cgbow
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
    c5
    clt
    breq2
    @3
    cN
    cgbow
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
    c6
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c6
    cN
    cle
    wbr
    #
    w3a
    @16
    c6
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
    c5
    c6
    clt
    wbr
    #
    @21
    @16
    5lt6
    @20
    c5
    cr
    wcel
    #
    c6
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
    5re
    a1i
    @24
    @20
    6re
    a1i
    cN
    zre
    c5
    c6
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
    cN
    vp
    cv
    #
    vq
    cv
    #
    caddc
    co
    vr
    cv
    #
    caddc
    co
    #
    wceq
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
    isgbow
    @31
    @15
    @1
    @30
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
    @29
    @15
    vr
    cprime
    @34
    @27
    cprime
    wcel
    #
    wa
    #
    @15
    @29
    @28
    @12
    wceq
    #
    vf
    @14
    wrex
    @36
    @37
    @28
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
    @38
    @14
    @36
    @38
    @14
    wcel
    #
    @8
    cprime
    @38
    wf
    #
    @36
    @8
    @25
    @26
    @27
    ctp
    #
    cprime
    @38
    @36
    c1
    c2
    c3
    ctp
    #
    @44
    @38
    wf
    #
    @8
    @44
    @38
    wf
    @46
    @36
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
    @45
    @44
    @38
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
    @52
    ctp
    #
    @45
    c3
    @52
    c1
    cfz
    @52
    c3
    1p2e3
    eqcomi
    oveq2i
    c1
    cz
    wcel
    #
    @53
    @55
    wceq
    1z
    c1
    fztp
    ax-mp
    c1
    c1
    wceq
    #
    @55
    @45
    wceq
    c1
    eqid
    @57
    c1
    c1
    @54
    c2
    @52
    c3
    @57
    id
    @54
    c2
    wceq
    @57
    1p1e2
    a1i
    @52
    c3
    wceq
    @57
    1p2e3
    a1i
    tpeq123d
    ax-mp
    3eqtri
    #
    feq2i
    sylibr
    @32
    @33
    @35
    w3a
    @36
    @44
    cprime
    wss
    @32
    @33
    @35
    df-3an
    @25
    @26
    @27
    cprime
    @47
    @48
    @49
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
    @42
    @43
    wb
    @36
    @59
    @60
    prmex
    c1
    c3
    cfz
    ovex
    pm3.2i
    cprime
    @8
    @38
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    @10
    @38
    wceq
    #
    @37
    @41
    wb
    @36
    @61
    @12
    @40
    @28
    @61
    @8
    @11
    @39
    vk
    @9
    @10
    @38
    fveq1
    sumeq2sdv
    eqeq2d
    adantl
    @36
    @40
    @45
    @39
    vk
    csu
    @28
    @36
    @8
    @45
    @39
    vk
    @8
    @45
    wceq
    @36
    @58
    a1i
    sumeq1d
    @36
    c1
    c2
    c3
    @39
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
    @39
    c1
    @38
    cfv
    #
    @25
    @9
    c1
    @38
    fveq2
    c1
    c2
    wne
    #
    c1
    c3
    wne
    #
    @62
    @25
    wceq
    1ne2
    @50
    c1
    c2
    c3
    @25
    @26
    @27
    1ex
    @47
    fvtp1
    mp2an
    syl6eq
    @9
    c2
    wceq
    @39
    c2
    @38
    cfv
    #
    @26
    @9
    c2
    @38
    fveq2
    @63
    c2
    c3
    wne
    #
    @65
    @26
    wceq
    1ne2
    @51
    c1
    c2
    c3
    @25
    @26
    @27
    2ex
    @48
    fvtp2
    mp2an
    syl6eq
    @9
    c3
    wceq
    @39
    c3
    @38
    cfv
    #
    @27
    @9
    c3
    @38
    fveq2
    @64
    @66
    @67
    @27
    wceq
    @50
    @51
    c1
    c2
    c3
    @25
    @26
    @27
    3ex
    @49
    fvtp3
    mp2an
    syl6eq
    @32
    @33
    @35
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
    @32
    @68
    @33
    @69
    @35
    @70
    @32
    @25
    @25
    prmz
    zcnd
    @33
    @26
    @26
    prmz
    zcnd
    @35
    @27
    @27
    prmz
    zcnd
    3anim123i
    3expa
    @56
    c2
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    w3a
    @36
    @56
    @71
    @72
    1z
    2z
    3z
    3pm3.2i
    a1i
    @63
    @36
    1ne2
    a1i
    @64
    @36
    @50
    a1i
    @66
    @36
    @51
    a1i
    sumtp
    eqtr2d
    rspcedvd
    @29
    @13
    @37
    vf
    @14
    cN
    @28
    @12
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    rexlimivv
    adantl
    sylbi
    a1i
    3syld
    com12
end
