include "cgbe.mm"
include "wcel.mm"
include "ceven.mm"
include "cv.mm"
include "codd.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "wa.mm"
include "c3.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "cfv.mm"
include "csu.mm"
include "cmap.mm"
include "cn.mm"
include "isgbe.mm"
include "wi.mm"
include "c2.mm"
include "cpr.mm"
include "2nn.mm"
include "a1i.mm"
include "wb.mm"
include "oveq2.mm"
include "df-2.mm"
include "oveq2i.mm"
include "cz.mm"
include "1z.mm"
include "fzpr.mm"
include "ax-mp.mm"
include "1p1e2.mm"
include "preq2i.mm"
include "3eqtri.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "breq1.mm"
include "sumeq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "adantl.mm"
include "cop.mm"
include "wf.mm"
include "wne.mm"
include "1ne2.mm"
include "1ex.mm"
include "2ex.mm"
include "vex.mm"
include "fpr.mm"
include "mp1i.mm"
include "prssi.mm"
include "fssd.mm"
include "cvv.mm"
include "prmex.mm"
include "prex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mpbird.mm"
include "fveq1.mm"
include "adantr.mm"
include "sumeq2dv.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "prmz.mm"
include "fveq2.mm"
include "fvpr1.mm"
include "fvpr2.mm"
include "cc.mm"
include "zcn.mm"
include "anim12i.mm"
include "sumpr.mm"
include "syl2an.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "jctil.mm"
include "rspcedvd.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "3ad2ant3.mm"
include "a1d.mm"
include "ex.mm"
include "rexlimivv.mm"
include "impcom.mm"
include "sylbi.mm"

theorem nnsum3primesgbe
  let vf: setvar f
  let vk: setvar k
  let cN: class N
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x

  disjoint N d
  disjoint N f
  disjoint N k
  disjoint d f
  disjoint d k
  disjoint f k
  disjoint N p
  disjoint N q
  disjoint d p
  disjoint d q
  disjoint f p
  disjoint f q
  disjoint k p
  disjoint k q
  disjoint p q
  disjoint k x
  assert |- ( N e. GoldbachEven -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 3 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    cN
    cgbe
    wcel
    cN
    ceven
    wcel
    #
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    cN
    @1
    @3
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    wa
    vd
    cv
    #
    c3
    cle
    wbr
    #
    cN
    c1
    @9
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
    wa
    #
    vf
    cprime
    @11
    cmap
    co
    #
    wrex
    #
    vd
    cn
    wrex
    #
    cN
    vq
    vp
    isgbe
    @8
    @0
    @20
    @7
    @0
    @20
    wi
    #
    vp
    vq
    cprime
    cprime
    @1
    cprime
    wcel
    #
    @3
    cprime
    wcel
    #
    wa
    #
    @7
    @21
    @24
    @7
    wa
    #
    @20
    @0
    @25
    @19
    c2
    c3
    cle
    wbr
    #
    cN
    c1
    c2
    cpr
    #
    @14
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @27
    cmap
    co
    #
    wrex
    #
    vd
    c2
    cn
    c2
    cn
    wcel
    #
    @25
    2nn
    a1i
    @9
    c2
    wceq
    #
    @19
    @32
    wb
    @25
    @34
    @17
    @30
    vf
    @18
    @31
    @34
    @11
    @27
    cprime
    cmap
    @34
    @11
    c1
    c2
    cfz
    co
    #
    @27
    @9
    c2
    c1
    cfz
    oveq2
    @35
    c1
    c1
    c1
    caddc
    co
    #
    cfz
    co
    #
    c1
    @36
    cpr
    #
    @27
    c2
    @36
    c1
    cfz
    df-2
    oveq2i
    c1
    cz
    wcel
    #
    @37
    @38
    wceq
    1z
    c1
    fzpr
    ax-mp
    @36
    c2
    c1
    1p1e2
    preq2i
    3eqtri
    syl6eq
    #
    oveq2d
    @34
    @10
    @26
    @16
    @29
    @9
    c2
    c3
    cle
    breq1
    @34
    @15
    @28
    cN
    @34
    @11
    @27
    @14
    vk
    @40
    sumeq1d
    eqeq2d
    anbi12d
    rexeqbidv
    adantl
    @25
    @32
    @26
    @28
    @5
    wceq
    #
    wa
    #
    vf
    @31
    wrex
    #
    @24
    @43
    @7
    @24
    @42
    @26
    @27
    @12
    c1
    @1
    cop
    c2
    @3
    cop
    cpr
    #
    cfv
    #
    vk
    csu
    #
    @5
    wceq
    #
    wa
    #
    vf
    @44
    @31
    @24
    @44
    @31
    wcel
    #
    @27
    cprime
    @44
    wf
    #
    @24
    @27
    @1
    @3
    cpr
    #
    cprime
    @44
    c1
    c2
    wne
    #
    @27
    @51
    @44
    wf
    @24
    1ne2
    c1
    c2
    @1
    @3
    1ex
    2ex
    vp
    vex
    #
    vq
    vex
    #
    fpr
    mp1i
    @1
    @3
    cprime
    prssi
    fssd
    cprime
    cvv
    wcel
    #
    @27
    cvv
    wcel
    #
    wa
    @49
    @50
    wb
    @24
    @55
    @56
    prmex
    c1
    c2
    prex
    pm3.2i
    cprime
    @27
    @44
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    @13
    @44
    wceq
    #
    @42
    @48
    wb
    @24
    @57
    @41
    @47
    @26
    @57
    @28
    @46
    @5
    @57
    @27
    @14
    @45
    vk
    @57
    @14
    @45
    wceq
    @12
    @27
    wcel
    @12
    @13
    @44
    fveq1
    adantr
    sumeq2dv
    eqeq1d
    anbi2d
    adantl
    @24
    @47
    @26
    @22
    @1
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @47
    @23
    @1
    prmz
    @3
    prmz
    @58
    @59
    wa
    #
    c1
    c2
    @45
    @1
    vk
    @3
    cz
    cn
    @12
    c1
    wceq
    @45
    c1
    @44
    cfv
    #
    @1
    @12
    c1
    @44
    fveq2
    @52
    @61
    @1
    wceq
    1ne2
    c1
    c2
    @1
    @3
    1ex
    @53
    fvpr1
    ax-mp
    syl6eq
    @12
    c2
    wceq
    @45
    c2
    @44
    cfv
    #
    @3
    @12
    c2
    @44
    fveq2
    @52
    @62
    @3
    wceq
    1ne2
    c1
    c2
    @1
    @3
    2ex
    @54
    fvpr2
    ax-mp
    syl6eq
    @58
    @1
    cc
    wcel
    @59
    @3
    cc
    wcel
    @1
    zcn
    @3
    zcn
    anim12i
    @39
    @33
    wa
    @60
    @39
    @33
    1z
    2nn
    pm3.2i
    a1i
    @52
    @60
    1ne2
    a1i
    sumpr
    syl2an
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    jctil
    rspcedvd
    adantr
    @7
    @32
    @43
    wb
    #
    @24
    @6
    @2
    @63
    @4
    @6
    @30
    @42
    vf
    @31
    @6
    @29
    @41
    @26
    @6
    @29
    @5
    @28
    wceq
    @41
    cN
    @5
    @28
    eqeq1
    @5
    @28
    eqcom
    syl6bb
    anbi2d
    rexbidv
    3ad2ant3
    adantl
    mpbird
    rspcedvd
    a1d
    ex
    rexlimivv
    impcom
    sylbi
end
