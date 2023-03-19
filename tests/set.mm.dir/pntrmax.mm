include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "wral.mm"
include "wrex.mm"
include "wtru.mm"
include "c1.mm"
include "cchp.mm"
include "caddc.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "a1i.mm"
include "1red.mm"
include "wcel.mm"
include "cc.mm"
include "cmin.mm"
include "pntrval.mm"
include "rpre.mm"
include "chpcl.mm"
include "syl.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "recnd.mm"
include "adantl.mm"
include "cmpt.mm"
include "co1.mm"
include "oveq1d.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divsubdird.mm"
include "dividd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "mpteq2ia.mm"
include "wa.mm"
include "chpo1ub.mm"
include "ax-1cn.mm"
include "o1const.mm"
include "mp2an.mm"
include "o1sub2.mm"
include "syl5eqel.mm"
include "peano2re.mm"
include "ad2antrl.mm"
include "clt.mm"
include "w3a.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "fveq2d.mm"
include "cc0.mm"
include "1re.mm"
include "3ad2ant2.mm"
include "resubcl.mm"
include "sylancr.mm"
include "0red.mm"
include "chpge0.mm"
include "wb.mm"
include "addge02.mm"
include "mpbid.mm"
include "suble0.mm"
include "mpbird.mm"
include "rpregt0.mm"
include "divge0.mm"
include "syl21anc.mm"
include "letrd.mm"
include "c2.mm"
include "2re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "adantr.mm"
include "simpr.mm"
include "1lt2.mm"
include "lelttrd.mm"
include "chpeq0.mm"
include "wne.mm"
include "simp1.mm"
include "rpcnne0d.mm"
include "div0.mm"
include "eqbrtrd.mm"
include "wi.mm"
include "0lt1.mm"
include "lediv2a.mm"
include "ex.mm"
include "syl212anc.mm"
include "imp.mm"
include "div1d.mm"
include "breqtrd.mm"
include "simp2.mm"
include "ltle.mm"
include "sylan.mm"
include "3impia.mm"
include "chpwordi.mm"
include "syl3anc.mm"
include "lecasei.mm"
include "cn0.mm"
include "2nn0.mm"
include "nn0addge1.mm"
include "df-2.mm"
include "oveq2i.mm"
include "add12d.mm"
include "syl5eq.mm"
include "absdifled.mm"
include "mpbir2and.mm"
include "3expb.mm"
include "adantrlr.mm"
include "adantll.mm"
include "o1bddrp.mm"
include "trud.mm"

theorem pntrmax
  let vx: setvar x
  let cR: class R
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cA: class A
  let vb: setvar b
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a x
  disjoint c x
  disjoint R c
  disjoint R x
  disjoint a d
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint A a
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint c d
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c y
  disjoint d y
  disjoint R d
  disjoint k y
  disjoint R k
  disjoint m y
  disjoint R m
  disjoint n y
  disjoint R n
  disjoint x y
  disjoint R y
  assert |- E. c e. RR+ A. x e. RR+ ( abs ` ( ( R ` x ) / x ) ) <_ c

  proof
    vx
    cv
    #
    cR
    cfv
    #
    @0
    cdiv
    co
    #
    cabs
    cfv
    #
    vc
    cv
    cle
    wbr
    vx
    crp
    wral
    vc
    crp
    wrex
    wtru
    vx
    vy
    crp
    @2
    c1
    vc
    vy
    cv
    #
    cchp
    cfv
    #
    c1
    caddc
    co
    #
    crp
    cr
    wss
    #
    wtru
    rpssre
    a1i
    wtru
    1red
    @0
    crp
    wcel
    #
    @2
    cc
    wcel
    wtru
    @8
    @2
    @1
    cr
    wcel
    @8
    @2
    cr
    wcel
    @8
    @1
    @0
    cchp
    cfv
    #
    @0
    cmin
    co
    #
    cr
    @0
    cR
    va
    pntrval.r
    pntrval
    #
    @8
    @9
    @0
    @8
    @0
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @0
    rpre
    #
    @0
    chpcl
    syl
    #
    @14
    resubcld
    eqeltrd
    @1
    @0
    rerpdivcl
    mpancom
    recnd
    adantl
    wtru
    vx
    crp
    @2
    cmpt
    vx
    crp
    @9
    @0
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cmpt
    co1
    vx
    crp
    @2
    @17
    @8
    @2
    @10
    @0
    cdiv
    co
    @16
    @0
    @0
    cdiv
    co
    #
    cmin
    co
    @17
    @8
    @1
    @10
    @0
    cdiv
    @11
    oveq1d
    @8
    @9
    @0
    @0
    @8
    @9
    @15
    recnd
    @0
    rpcn
    #
    @19
    @0
    rpne0
    #
    divsubdird
    @8
    @18
    c1
    @16
    cmin
    @8
    @0
    @19
    @20
    dividd
    oveq2d
    3eqtrd
    #
    mpteq2ia
    wtru
    vx
    crp
    @16
    c1
    cr
    @8
    @16
    cr
    wcel
    #
    wtru
    @13
    @8
    @22
    @15
    @9
    @0
    rerpdivcl
    mpancom
    #
    adantl
    wtru
    @8
    wa
    1red
    vx
    crp
    @16
    cmpt
    co1
    wcel
    wtru
    vx
    chpo1ub
    a1i
    vx
    crp
    c1
    cmpt
    co1
    wcel
    #
    wtru
    @7
    c1
    cc
    wcel
    #
    @24
    rpssre
    ax-1cn
    vx
    crp
    c1
    o1const
    mp2an
    a1i
    o1sub2
    syl5eqel
    @4
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wtru
    c1
    @4
    cle
    wbr
    #
    @26
    @5
    cr
    wcel
    #
    @27
    @4
    chpcl
    #
    @5
    peano2re
    syl
    #
    ad2antrl
    @8
    @26
    @28
    wa
    @0
    @4
    clt
    wbr
    #
    wa
    @3
    @6
    cle
    wbr
    #
    wtru
    @8
    @26
    @32
    @33
    @28
    @8
    @26
    @32
    @33
    @8
    @26
    @32
    w3a
    #
    @3
    @17
    cabs
    cfv
    #
    @6
    cle
    @34
    @2
    @17
    cabs
    @8
    @26
    @2
    @17
    wceq
    @32
    @21
    3ad2ant1
    fveq2d
    @34
    @35
    @6
    cle
    wbr
    c1
    @6
    cmin
    co
    #
    @16
    cle
    wbr
    @16
    c1
    @6
    caddc
    co
    #
    cle
    wbr
    @34
    @36
    cc0
    @16
    @34
    c1
    cr
    wcel
    #
    @27
    @36
    cr
    wcel
    1re
    @26
    @8
    @27
    @32
    @31
    3ad2ant2
    #
    c1
    @6
    resubcl
    sylancr
    @34
    0red
    @8
    @26
    @22
    @32
    @23
    3ad2ant1
    #
    @34
    @36
    cc0
    cle
    wbr
    #
    c1
    @6
    cle
    wbr
    #
    @34
    cc0
    @5
    cle
    wbr
    #
    @42
    @26
    @8
    @43
    @32
    @4
    chpge0
    3ad2ant2
    #
    @34
    @38
    @29
    @43
    @42
    wb
    1re
    @26
    @8
    @29
    @32
    @30
    3ad2ant2
    #
    c1
    @5
    addge02
    sylancr
    mpbid
    @34
    @38
    @27
    @41
    @42
    wb
    1re
    @39
    c1
    @6
    suble0
    sylancr
    mpbird
    @34
    @13
    cc0
    @9
    cle
    wbr
    #
    @12
    cc0
    @0
    clt
    wbr
    wa
    #
    cc0
    @16
    cle
    wbr
    @8
    @26
    @13
    @32
    @15
    3ad2ant1
    #
    @34
    @12
    @46
    @8
    @26
    @12
    @32
    @14
    3ad2ant1
    #
    @0
    chpge0
    syl
    #
    @8
    @26
    @47
    @32
    @0
    rpregt0
    3ad2ant1
    #
    @9
    @0
    divge0
    syl21anc
    letrd
    @34
    @16
    @5
    c2
    caddc
    co
    #
    @37
    cle
    @34
    @16
    @5
    @52
    @40
    @45
    @34
    @29
    c2
    cr
    wcel
    #
    @52
    cr
    wcel
    @45
    2re
    @5
    c2
    readdcl
    sylancl
    @34
    @16
    @5
    cle
    wbr
    @0
    c1
    @49
    @34
    1red
    #
    @34
    @0
    c1
    cle
    wbr
    #
    wa
    #
    @16
    cc0
    @0
    cdiv
    co
    #
    @5
    cle
    @56
    @9
    cc0
    @0
    cdiv
    @56
    @9
    cc0
    wceq
    #
    @0
    c2
    clt
    wbr
    #
    @56
    @0
    c1
    c2
    @34
    @12
    @55
    @49
    adantr
    #
    @56
    1red
    @53
    @56
    2re
    a1i
    @34
    @55
    simpr
    c1
    c2
    clt
    wbr
    @56
    1lt2
    a1i
    lelttrd
    @56
    @12
    @58
    @59
    wb
    @60
    @0
    chpeq0
    syl
    mpbird
    oveq1d
    @34
    @57
    @5
    cle
    wbr
    @55
    @34
    @57
    cc0
    @5
    cle
    @34
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    @57
    cc0
    wceq
    @34
    @0
    @8
    @26
    @32
    simp1
    rpcnne0d
    @0
    div0
    syl
    @44
    eqbrtrd
    adantr
    eqbrtrd
    @34
    c1
    @0
    cle
    wbr
    #
    wa
    #
    @16
    @9
    @5
    @34
    @22
    @61
    @40
    adantr
    @34
    @13
    @61
    @48
    adantr
    #
    @34
    @29
    @61
    @45
    adantr
    @62
    @16
    @9
    c1
    cdiv
    co
    #
    @9
    cle
    @34
    @61
    @16
    @64
    cle
    wbr
    #
    @34
    @38
    cc0
    c1
    clt
    wbr
    #
    @47
    @13
    @46
    @61
    @65
    wi
    @54
    @66
    @34
    0lt1
    a1i
    @51
    @48
    @50
    @38
    @66
    wa
    @47
    @13
    @46
    wa
    w3a
    @61
    @65
    c1
    @0
    @9
    lediv2a
    ex
    syl212anc
    imp
    @62
    @9
    @62
    @9
    @63
    recnd
    div1d
    breqtrd
    @34
    @9
    @5
    cle
    wbr
    #
    @61
    @34
    @12
    @26
    @0
    @4
    cle
    wbr
    #
    @67
    @49
    @8
    @26
    @32
    simp2
    @8
    @26
    @32
    @68
    @8
    @12
    @26
    @32
    @68
    wi
    @14
    @0
    @4
    ltle
    sylan
    3impia
    @0
    @4
    chpwordi
    syl3anc
    adantr
    letrd
    lecasei
    @34
    @29
    c2
    cn0
    wcel
    @5
    @52
    cle
    wbr
    @45
    2nn0
    @5
    c2
    nn0addge1
    sylancl
    letrd
    @34
    @52
    @5
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @37
    c2
    @69
    @5
    caddc
    df-2
    oveq2i
    @34
    @5
    c1
    c1
    @34
    @5
    @45
    recnd
    @25
    @34
    ax-1cn
    a1i
    #
    @70
    add12d
    syl5eq
    breqtrd
    @34
    @16
    c1
    @6
    @40
    @54
    @39
    absdifled
    mpbir2and
    eqbrtrd
    3expb
    adantrlr
    adantll
    o1bddrp
    trud
end
