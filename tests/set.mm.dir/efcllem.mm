include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cfl.mm"
include "cuz.mm"
include "cn0.mm"
include "nn0uz.mm"
include "eqid.mm"
include "cr.mm"
include "halfre.mm"
include "a1i.mm"
include "clt.mm"
include "wbr.mm"
include "halflt1.mm"
include "cle.mm"
include "2re.mm"
include "abscl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "absge0.mm"
include "wa.mm"
include "0le2.mm"
include "mulge0.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "flge0nn0.mm"
include "cv.mm"
include "cexp.mm"
include "cfa.mm"
include "wceq.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "eqeltrd.mm"
include "caddc.mm"
include "adantr.mm"
include "cn.mm"
include "eluznn0.mm"
include "sylan.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "nndivred.mm"
include "reexpcld.mm"
include "faccl.mm"
include "expcl.mm"
include "syldan.mm"
include "absge0d.mm"
include "absexp.mm"
include "breqtrd.mm"
include "nnred.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "flltp1.mm"
include "eluzp1p1.mm"
include "eluzle.mm"
include "ltletrd.mm"
include "recnd.mm"
include "2cn.mm"
include "mulcom.mm"
include "sylancl.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "1red.mm"
include "jca.mm"
include "lt2mul2div.mm"
include "mpbid.mm"
include "wi.mm"
include "ltle.mm"
include "mpd.mm"
include "lemul2ad.mm"
include "fveq2d.mm"
include "expp1d.mm"
include "eqtrd.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "facp1.mm"
include "oveq12d.mm"
include "nnne0d.mm"
include "absdivd.mm"
include "divmuldivd.mm"
include "3eqtr4d.mm"
include "halfcn.mm"
include "abscld.mm"
include "eftabs.mm"
include "oveq1d.mm"
include "cvgrat.mm"

theorem efcllem
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let cN: class N
  assume eftval.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint A n
  disjoint k n
  disjoint A k
  disjoint F k
  disjoint N n
  assert |- ( A e. CC -> seq 0 ( + , F ) e. dom ~~> )

  proof
    cA
    cc
    wcel
    #
    c1
    c2
    cdiv
    co
    #
    vk
    cF
    cc0
    c2
    cA
    cabs
    cfv
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @4
    cuz
    cfv
    #
    cn0
    nn0uz
    @5
    eqid
    @1
    cr
    wcel
    #
    @0
    halfre
    a1i
    @1
    c1
    clt
    wbr
    @0
    halflt1
    a1i
    @0
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @4
    cn0
    wcel
    #
    @0
    c2
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @7
    2re
    cA
    abscl
    #
    c2
    @2
    remulcl
    sylancr
    #
    @0
    @11
    cc0
    @2
    cle
    wbr
    #
    @8
    @12
    cA
    absge0
    @10
    cc0
    c2
    cle
    wbr
    @11
    @14
    wa
    @8
    2re
    0le2
    c2
    @2
    mulge0
    mpanl12
    syl2anc
    @3
    flge0nn0
    syl2anc
    #
    @0
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    @16
    cF
    cfv
    #
    cA
    @16
    cexp
    co
    #
    @16
    cfa
    cfv
    #
    cdiv
    co
    #
    cc
    @17
    @18
    @21
    wceq
    #
    @0
    cA
    vn
    cF
    @16
    eftval.1
    eftval
    #
    adantl
    cA
    @16
    eftcl
    eqeltrd
    #
    @0
    @16
    @5
    wcel
    #
    wa
    #
    @2
    @16
    cexp
    co
    #
    @20
    cdiv
    co
    #
    @2
    @16
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @28
    @1
    cmul
    co
    #
    @29
    cF
    cfv
    #
    cabs
    cfv
    #
    @1
    @18
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    @26
    @30
    @1
    @28
    @26
    @2
    @29
    @0
    @11
    @25
    @12
    adantr
    #
    @26
    @17
    @29
    cn
    wcel
    @0
    @9
    @25
    @17
    @15
    @16
    @4
    eluznn0
    sylan
    #
    @16
    nn0p1nn
    syl
    #
    nndivred
    #
    @6
    @26
    halfre
    a1i
    @26
    @27
    @20
    @26
    @2
    @16
    @37
    @38
    reexpcld
    #
    @26
    @17
    @20
    cn
    wcel
    @38
    @16
    faccl
    syl
    #
    nndivred
    @26
    @27
    cr
    wcel
    cc0
    @27
    cle
    wbr
    @20
    cr
    wcel
    cc0
    @20
    clt
    wbr
    cc0
    @28
    cle
    wbr
    @41
    @26
    cc0
    @19
    cabs
    cfv
    #
    @27
    cle
    @26
    @19
    @0
    @25
    @17
    @19
    cc
    wcel
    @38
    cA
    @16
    expcl
    syldan
    absge0d
    @0
    @25
    @17
    @43
    @27
    wceq
    @38
    cA
    @16
    absexp
    syldan
    breqtrd
    @26
    @20
    @42
    nnred
    @26
    @20
    @42
    nngt0d
    @27
    @20
    divge0
    syl22anc
    @26
    @30
    @1
    clt
    wbr
    #
    @30
    @1
    cle
    wbr
    #
    @26
    @2
    c2
    cmul
    co
    #
    c1
    @29
    cmul
    co
    #
    clt
    wbr
    #
    @44
    @26
    @3
    @29
    @46
    @47
    clt
    @26
    @3
    @4
    c1
    caddc
    co
    #
    @29
    @0
    @7
    @25
    @13
    adantr
    #
    @0
    @49
    cr
    wcel
    @25
    @0
    @49
    @0
    @9
    @49
    cn0
    wcel
    @15
    @4
    peano2nn0
    syl
    nn0red
    adantr
    @26
    @29
    @39
    nnred
    #
    @26
    @7
    @3
    @49
    clt
    wbr
    @50
    @3
    flltp1
    syl
    @26
    @29
    @49
    cuz
    cfv
    wcel
    #
    @49
    @29
    cle
    wbr
    @25
    @52
    @0
    @4
    @16
    eluzp1p1
    adantl
    @49
    @29
    eluzle
    syl
    ltletrd
    @26
    @2
    cc
    wcel
    c2
    cc
    wcel
    @46
    @3
    wceq
    @26
    @2
    @37
    recnd
    #
    2cn
    @2
    c2
    mulcom
    sylancl
    @26
    @29
    @26
    @29
    @39
    nncnd
    #
    mulid2d
    3brtr4d
    @26
    @11
    @10
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    c1
    cr
    wcel
    @29
    cr
    wcel
    #
    cc0
    @29
    clt
    wbr
    #
    wa
    @48
    @44
    wb
    @37
    @56
    @26
    @10
    @55
    2re
    2pos
    pm3.2i
    a1i
    @26
    1red
    @26
    @57
    @58
    @51
    @26
    @29
    @39
    nngt0d
    jca
    @2
    c2
    c1
    @29
    lt2mul2div
    syl22anc
    mpbid
    @26
    @30
    cr
    wcel
    @6
    @44
    @45
    wi
    @40
    halfre
    @30
    @1
    ltle
    sylancl
    mpd
    lemul2ad
    @26
    @34
    cA
    @29
    cexp
    co
    #
    @29
    cfa
    cfv
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    @31
    @26
    @33
    @61
    cabs
    @26
    @29
    cn0
    wcel
    #
    @33
    @61
    wceq
    @26
    @17
    @63
    @38
    @16
    peano2nn0
    syl
    #
    cA
    vn
    cF
    @29
    eftval.1
    eftval
    syl
    fveq2d
    @26
    @59
    cabs
    cfv
    #
    @60
    cabs
    cfv
    #
    cdiv
    co
    @27
    @2
    cmul
    co
    #
    @20
    @29
    cmul
    co
    #
    cdiv
    co
    @62
    @31
    @26
    @65
    @67
    @66
    @68
    cdiv
    @26
    @65
    @2
    @29
    cexp
    co
    #
    @67
    @0
    @25
    @63
    @65
    @69
    wceq
    @64
    cA
    @29
    absexp
    syldan
    @26
    @2
    @16
    @53
    @38
    expp1d
    eqtrd
    @26
    @66
    @60
    @68
    @26
    @60
    @26
    @60
    @26
    @63
    @60
    cn
    wcel
    @64
    @29
    faccl
    syl
    #
    nnred
    @26
    @60
    @26
    @60
    @70
    nnnn0d
    nn0ge0d
    absidd
    @26
    @17
    @60
    @68
    wceq
    @38
    @16
    facp1
    syl
    eqtrd
    oveq12d
    @26
    @59
    @60
    @0
    @25
    @63
    @59
    cc
    wcel
    @64
    cA
    @29
    expcl
    syldan
    @26
    @60
    @70
    nncnd
    @26
    @60
    @70
    nnne0d
    absdivd
    @26
    @27
    @20
    @2
    @29
    @26
    @27
    @41
    recnd
    @26
    @20
    @42
    nncnd
    @53
    @54
    @26
    @20
    @42
    nnne0d
    @26
    @29
    @39
    nnne0d
    divmuldivd
    3eqtr4d
    eqtrd
    @26
    @36
    @35
    @1
    cmul
    co
    #
    @32
    @26
    @1
    cc
    wcel
    @35
    cc
    wcel
    @36
    @71
    wceq
    halfcn
    @26
    @35
    @26
    @18
    @0
    @25
    @17
    @18
    cc
    wcel
    @38
    @24
    syldan
    abscld
    recnd
    @1
    @35
    mulcom
    sylancr
    @26
    @35
    @28
    @1
    cmul
    @26
    @35
    @21
    cabs
    cfv
    #
    @28
    @26
    @18
    @21
    cabs
    @26
    @17
    @22
    @38
    @23
    syl
    fveq2d
    @0
    @25
    @17
    @72
    @28
    wceq
    @38
    cA
    @16
    eftabs
    syldan
    eqtrd
    oveq1d
    eqtrd
    3brtr4d
    cvgrat
end
