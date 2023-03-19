include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "cn0.mm"
include "c1.mm"
include "cif.mm"
include "wcel.mm"
include "wceq.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nnred.mm"
include "remulcld.mm"
include "adantr.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "2pos.mm"
include "nngt0d.mm"
include "mulgt0d.mm"
include "gt0ne0d.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "expnegd.mm"
include "adantrr.mm"
include "crp.mm"
include "2rp.mm"
include "jca.mm"
include "rpmulcl.mm"
include "syl.mm"
include "elrpd.mm"
include "rpexpcld.mm"
include "rprecred.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "abscld.mm"
include "nnnn0.mm"
include "reexpcld.mm"
include "rpred.mm"
include "rpne0d.mm"
include "redivcld.mm"
include "ifcld.mm"
include "max1.mm"
include "simprr.mm"
include "lelttrd.mm"
include "cc.mm"
include "mulexpd.mm"
include "1red.mm"
include "rpge0d.mm"
include "w3a.mm"
include "absge0d.mm"
include "simprd.mm"
include "ltled.mm"
include "3jca.mm"
include "exple1.mm"
include "lemul2ad.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "ltletrd.mm"
include "ltrec1d.mm"
include "wb.mm"
include "nnnegz.mm"
include "reexpclzd.mm"
include "ltdivmuld.mm"
include "mpbird.mm"
include "max2.mm"
include "letrd.mm"
include "ledivmul2d.mm"
include "mpbid.mm"
include "1t1e1.mm"
include "eqcomi.mm"
include "0le1.mm"
include "1lt2.mm"
include "ltmul12ad.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "expnbnd.mm"
include "reximddv.mm"
include "wss.mm"
include "wi.mm"
include "nnssnn0.mm"
include "ssrexv.mm"
include "ax-mp.mm"

theorem knoppndvlem18
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vj: setvar j
  let cE: class E
  let cG: class G
  let cN: class N
  assume knoppndvlem18.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem18.n: |- ( ph -> N e. NN )
  assume knoppndvlem18.d: |- ( ph -> D e. RR+ )
  assume knoppndvlem18.e: |- ( ph -> E e. RR+ )
  assume knoppndvlem18.g: |- ( ph -> G e. RR+ )
  assume knoppndvlem18.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )

  disjoint C j
  disjoint D j
  disjoint E j
  disjoint G j
  disjoint N j
  disjoint j ph
  assert |- ( ph -> E. j e. NN0 ( ( ( ( 2 x. N ) ^ -u j ) / 2 ) < D /\ E <_ ( ( ( ( 2 x. N ) x. ( abs ` C ) ) ^ j ) x. G ) ) )

  proof
    wph
    c2
    cN
    cmul
    co
    #
    vj
    cv
    #
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    cD
    clt
    wbr
    #
    cE
    @0
    cC
    cabs
    cfv
    #
    cmul
    co
    #
    @1
    cexp
    co
    #
    cG
    cmul
    co
    cle
    wbr
    #
    wa
    #
    vj
    cn
    wrex
    #
    @9
    vj
    cn0
    wrex
    #
    wph
    c1
    c2
    cD
    cmul
    co
    #
    cdiv
    co
    #
    cE
    cG
    cdiv
    co
    #
    cle
    wbr
    #
    @14
    @13
    cif
    #
    @7
    clt
    wbr
    #
    @9
    vj
    cn
    wph
    @1
    cn
    wcel
    #
    @17
    wa
    #
    wa
    #
    @4
    @8
    @20
    @4
    @3
    @12
    clt
    wbr
    #
    @20
    @3
    c1
    @0
    @1
    cexp
    co
    #
    cdiv
    co
    #
    @12
    clt
    wph
    @18
    @3
    @23
    wceq
    @17
    wph
    @18
    wa
    #
    @0
    @1
    @24
    @0
    wph
    @0
    cr
    wcel
    @18
    wph
    c2
    cN
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    cN
    knoppndvlem18.n
    nnred
    #
    remulcld
    #
    adantr
    #
    recnd
    #
    wph
    @0
    cc0
    wne
    @18
    wph
    @0
    wph
    c2
    cN
    @25
    @26
    cc0
    c2
    clt
    wbr
    wph
    2pos
    a1i
    wph
    cN
    knoppndvlem18.n
    nngt0d
    mulgt0d
    #
    gt0ne0d
    adantr
    #
    @18
    @1
    cz
    wcel
    wph
    @1
    nnz
    adantl
    #
    expnegd
    adantrr
    @20
    @12
    @22
    wph
    @12
    crp
    wcel
    #
    @19
    wph
    c2
    crp
    wcel
    #
    cD
    crp
    wcel
    #
    wa
    @33
    wph
    @34
    @35
    @34
    wph
    2rp
    a1i
    knoppndvlem18.d
    jca
    c2
    cD
    rpmulcl
    syl
    #
    adantr
    #
    wph
    @18
    @22
    crp
    wcel
    @17
    @24
    @0
    @1
    wph
    @0
    crp
    wcel
    @18
    wph
    @0
    @27
    @30
    elrpd
    adantr
    @32
    rpexpcld
    #
    adantrr
    #
    @20
    @13
    @7
    @22
    @20
    @12
    @37
    rprecred
    #
    wph
    @18
    @7
    cr
    wcel
    @17
    @24
    @6
    @1
    wph
    @6
    cr
    wcel
    #
    @18
    wph
    @0
    @5
    @27
    wph
    cC
    wph
    cC
    wph
    cC
    cr
    wcel
    #
    @5
    c1
    clt
    wbr
    #
    wph
    cC
    knoppndvlem18.c
    knoppndvlem3
    #
    simpld
    recnd
    #
    abscld
    #
    remulcld
    #
    adantr
    @18
    @1
    cn0
    wcel
    #
    wph
    @1
    nnnn0
    adantl
    #
    reexpcld
    adantrr
    #
    @20
    @22
    @39
    rpred
    @20
    @13
    @16
    @7
    @40
    wph
    @16
    cr
    wcel
    #
    @19
    wph
    @15
    @14
    @13
    cr
    wph
    cE
    cG
    wph
    cE
    knoppndvlem18.e
    rpred
    #
    wph
    cG
    knoppndvlem18.g
    rpred
    wph
    cG
    knoppndvlem18.g
    rpne0d
    redivcld
    #
    wph
    @12
    @36
    rprecred
    #
    ifcld
    #
    adantr
    #
    @50
    wph
    @13
    @16
    cle
    wbr
    #
    @19
    wph
    @13
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    wa
    #
    @57
    wph
    @58
    @59
    @54
    @53
    jca
    #
    @13
    @14
    max1
    syl
    adantr
    wph
    @18
    @17
    simprr
    #
    lelttrd
    wph
    @18
    @7
    @22
    cle
    wbr
    @17
    @24
    @7
    @22
    @5
    @1
    cexp
    co
    #
    cmul
    co
    #
    @22
    cle
    @24
    @0
    @5
    @1
    @29
    wph
    @5
    cc
    wcel
    @18
    wph
    @5
    @46
    recnd
    #
    adantr
    @49
    mulexpd
    @24
    @64
    @22
    c1
    cmul
    co
    @22
    cle
    @24
    @63
    c1
    @22
    @24
    @5
    @1
    wph
    @5
    cr
    wcel
    #
    @18
    @46
    adantr
    @49
    reexpcld
    @24
    1red
    @24
    @22
    @38
    rpred
    #
    @24
    @22
    @38
    rpge0d
    @24
    @66
    cc0
    @5
    cle
    wbr
    #
    @5
    c1
    cle
    wbr
    #
    w3a
    #
    @48
    wa
    @63
    c1
    cle
    wbr
    @24
    @70
    @48
    wph
    @70
    @18
    wph
    @66
    @68
    @69
    @46
    wph
    cC
    @45
    absge0d
    wph
    @5
    c1
    @46
    wph
    1red
    #
    wph
    @42
    @43
    @44
    simprd
    ltled
    3jca
    adantr
    @49
    jca
    @5
    @1
    exple1
    syl
    lemul2ad
    @24
    @22
    @24
    @22
    @67
    recnd
    mulid1d
    breqtrd
    eqbrtrd
    adantrr
    ltletrd
    ltrec1d
    eqbrtrd
    wph
    @18
    @4
    @21
    wb
    @17
    @24
    @3
    cD
    c2
    @24
    @0
    @2
    @28
    @31
    @18
    @2
    cz
    wcel
    wph
    @1
    nnnegz
    adantl
    reexpclzd
    wph
    cD
    cr
    wcel
    @18
    wph
    cD
    knoppndvlem18.d
    rpred
    adantr
    @34
    @24
    2rp
    a1i
    ltdivmuld
    adantrr
    mpbird
    @20
    @14
    @7
    cle
    wbr
    @8
    @20
    @14
    @16
    @7
    wph
    @59
    @19
    @53
    adantr
    @56
    @50
    wph
    @14
    @16
    cle
    wbr
    #
    @19
    wph
    @60
    @72
    @61
    @13
    @14
    max2
    syl
    adantr
    @20
    @16
    @7
    @56
    @50
    @62
    ltled
    letrd
    @20
    cE
    @7
    cG
    wph
    cE
    cr
    wcel
    @19
    @52
    adantr
    @50
    wph
    cG
    crp
    wcel
    @19
    knoppndvlem18.g
    adantr
    ledivmul2d
    mpbid
    jca
    wph
    @51
    @41
    c1
    @6
    clt
    wbr
    #
    w3a
    @17
    vj
    cn
    wrex
    wph
    @51
    @41
    @73
    @55
    @47
    wph
    c1
    c2
    cN
    @5
    cmul
    co
    #
    cmul
    co
    #
    @6
    clt
    wph
    c1
    c1
    c1
    cmul
    co
    #
    @75
    clt
    c1
    @76
    wceq
    wph
    @76
    c1
    1t1e1
    eqcomi
    a1i
    wph
    c1
    c2
    c1
    @74
    @71
    @25
    @71
    wph
    cN
    @5
    @26
    @46
    remulcld
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    #
    c1
    c2
    clt
    wbr
    wph
    1lt2
    a1i
    @77
    knoppndvlem18.1
    ltmul12ad
    eqbrtrd
    wph
    @6
    @75
    wph
    c2
    cN
    @5
    wph
    c2
    @25
    recnd
    wph
    cN
    @26
    recnd
    @65
    mulassd
    eqcomd
    breqtrd
    3jca
    @16
    @6
    vj
    expnbnd
    syl
    reximddv
    cn
    cn0
    wss
    @10
    @11
    wi
    nnssnn0
    @9
    vj
    cn
    cn0
    ssrexv
    ax-mp
    syl
end
