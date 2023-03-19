include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cv.mm"
include "wceq.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "wa.mm"
include "wrex.mm"
include "eqidd.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "wwlknp.mm"
include "cmin.mm"
include "cfz.mm"
include "simprl.mm"
include "peano2nn0.mm"
include "syl.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "id.mm"
include "nn0p1nn.mm"
include "cr.mm"
include "nn0re.mm"
include "peano2re.mm"
include "3jca.mm"
include "ltp1d.mm"
include "lttr.mm"
include "imp.mm"
include "syl12anc.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "fz0add1fz1.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "adantl.mm"
include "mpbird.mm"
include "jca.mm"
include "3adantr3.mm"
include "swrd0fvlsw.mm"
include "lsw.mm"
include "3ad2ant1.mm"
include "preq12d.mm"
include "oveq1.mm"
include "3ad2ant2.mm"
include "fveq2d.mm"
include "preq2d.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "pncand.mm"
include "nn0cnd.mm"
include "eqtrd.mm"
include "wi.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "fzonn0p1.mm"
include "syl11.mm"
include "3ad2ant3.mm"
include "impcom.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "wwlksnred.mm"
include "eqeq2.mm"
include "preq1d.mm"
include "anbi12d.mm"
include "rspcedv.mm"
include "mp2and.mm"
include "ex.mm"

theorem wwlksnredwwlkn
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i
  assume wwlksnredwwlkn.e: |- E = ( Edg ` G )

  disjoint E y
  disjoint G y
  disjoint N y
  disjoint W y
  disjoint E i
  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( N e. NN0 -> ( W e. ( ( N + 1 ) WWalksN G ) -> E. y e. ( N WWalksN G ) ( ( W substr <. 0 , ( N + 1 ) >. ) = y /\ { ( lastS ` y ) , ( lastS ` W ) } e. E ) ) )

  proof
    cN
    cn0
    wcel
    #
    cW
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    wcel
    #
    cW
    cc0
    @1
    cop
    csubstr
    co
    #
    vy
    cv
    #
    wceq
    #
    @4
    clsw
    cfv
    #
    cW
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vy
    cN
    cG
    cwwlksn
    co
    #
    wrex
    #
    @0
    @2
    wa
    #
    @3
    @3
    wceq
    #
    @3
    clsw
    cfv
    #
    @7
    cpr
    #
    cE
    wcel
    #
    @12
    @13
    @3
    eqidd
    @2
    @0
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    @1
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    #
    @24
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @17
    vi
    cE
    cG
    @1
    @18
    cW
    @18
    eqid
    wwlksnredwwlkn.e
    wwlknp
    @0
    @32
    wa
    #
    @16
    @1
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @21
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cpr
    #
    cE
    @33
    @15
    @35
    @7
    @37
    @33
    @20
    @1
    c1
    @21
    cfz
    co
    #
    wcel
    #
    wa
    #
    @15
    @35
    wceq
    @0
    @20
    @23
    @41
    @31
    @0
    @20
    @23
    wa
    #
    wa
    #
    @20
    @40
    @0
    @20
    @23
    simprl
    @43
    @40
    @1
    c1
    @22
    cfz
    co
    #
    wcel
    #
    @0
    @45
    @42
    @0
    @22
    cn0
    wcel
    #
    cN
    cc0
    @22
    cfzo
    co
    wcel
    #
    @45
    @0
    @1
    cn0
    wcel
    #
    @46
    cN
    peano2nn0
    #
    @1
    peano2nn0
    syl
    @0
    @0
    @22
    cn
    wcel
    #
    cN
    @22
    clt
    wbr
    #
    @47
    @0
    id
    @0
    @48
    @50
    @49
    @1
    nn0p1nn
    syl
    @0
    cN
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    w3a
    #
    cN
    @1
    clt
    wbr
    #
    @1
    @22
    clt
    wbr
    #
    @51
    @0
    @52
    @55
    cN
    nn0re
    #
    @52
    @52
    @53
    @54
    @52
    id
    cN
    peano2re
    #
    @52
    @53
    @54
    @59
    @1
    peano2re
    syl
    3jca
    syl
    @0
    cN
    @58
    ltp1d
    @0
    @1
    @0
    @48
    @53
    @49
    @1
    nn0re
    syl
    ltp1d
    @55
    @56
    @57
    wa
    @51
    cN
    @1
    @22
    lttr
    imp
    syl12anc
    cN
    @22
    elfzo0
    syl3anbrc
    @22
    cN
    fz0add1fz1
    syl2anc
    adantr
    @42
    @40
    @45
    wb
    #
    @0
    @23
    @60
    @20
    @23
    @39
    @44
    @1
    @21
    @22
    c1
    cfz
    oveq2
    eleq2d
    adantl
    adantl
    mpbird
    jca
    3adantr3
    @1
    @18
    cW
    swrd0fvlsw
    syl
    @32
    @7
    @37
    wceq
    #
    @0
    @20
    @23
    @61
    @31
    cW
    @19
    lsw
    3ad2ant1
    adantl
    preq12d
    @33
    @38
    cN
    cW
    cfv
    #
    @1
    cW
    cfv
    #
    cpr
    #
    cE
    @33
    @38
    @35
    @22
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cpr
    #
    @64
    @33
    @37
    @66
    @35
    @33
    @36
    @65
    cW
    @32
    @36
    @65
    wceq
    #
    @0
    @23
    @20
    @68
    @31
    @21
    @22
    c1
    cmin
    oveq1
    3ad2ant2
    adantl
    fveq2d
    preq2d
    @0
    @67
    @64
    wceq
    @32
    @0
    @35
    @62
    @66
    @63
    @0
    @34
    cN
    cW
    @0
    cN
    c1
    cN
    nn0cn
    @0
    1cnd
    #
    pncand
    fveq2d
    @0
    @65
    @1
    cW
    @0
    @1
    c1
    @0
    @1
    @49
    nn0cnd
    @69
    pncand
    fveq2d
    preq12d
    adantr
    eqtrd
    @32
    @0
    @64
    cE
    wcel
    #
    @31
    @20
    @0
    @70
    wi
    @23
    cN
    @30
    wcel
    @31
    @70
    @0
    @29
    @70
    vi
    cN
    @30
    @24
    cN
    wceq
    #
    @28
    @64
    cE
    @71
    @25
    @62
    @27
    @63
    @24
    cN
    cW
    fveq2
    @71
    @26
    @1
    cW
    @24
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    rspcv
    cN
    fzonn0p1
    syl11
    3ad2ant3
    impcom
    eqeltrd
    eqeltrd
    sylan2
    @13
    @10
    @14
    @17
    wa
    #
    vy
    @3
    @11
    @0
    @2
    @3
    @11
    wcel
    cG
    cN
    cW
    wwlksnred
    imp
    @4
    @3
    wceq
    #
    @10
    @72
    wb
    @13
    @73
    @5
    @14
    @9
    @17
    @4
    @3
    @3
    eqeq2
    @73
    @8
    @16
    cE
    @73
    @6
    @15
    @7
    @4
    @3
    clsw
    fveq2
    preq1d
    eleq1d
    anbi12d
    adantl
    rspcedv
    mp2and
    ex
end
