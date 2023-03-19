include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "crp.mm"
include "c2.mm"
include "cfa.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "w3a.mm"
include "peano2nn.mm"
include "cdiv.mm"
include "cmpt.mm"
include "eqid.mm"
include "aaliou3lem3.mm"
include "3simpc.mm"
include "3syl.mm"
include "wceq.mm"
include "wb.mm"
include "cfz.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "nnuz.mm"
include "eqidd.mm"
include "weq.mm"
include "fveq2.mm"
include "negeqd.mm"
include "ovex.mm"
include "fvmpt.mm"
include "cz.mm"
include "2rp.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "syl.mm"
include "nnzd.mm"
include "znegcld.mm"
include "rpexpcl.mm"
include "sylancr.mm"
include "rpcnd.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "1nn.mm"
include "simp1d.mm"
include "mp1i.mm"
include "isumsplit.mm"
include "oveq2.mm"
include "sumex.mm"
include "3eqtr4rd.mm"
include "syl6eqr.mm"
include "aaliou3lem4.mm"
include "recni.mm"
include "a1i.mm"
include "aaliou3lem5.mm"
include "recnd.mm"
include "simp2d.mm"
include "subaddd.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "cr.mm"
include "adantr.mm"
include "clt.mm"
include "simprl.mm"
include "difrp.mm"
include "ltned.mm"
include "rpmulcl.mm"
include "rpred.mm"
include "resubcld.mm"
include "ltsubrpd.mm"
include "lttrd.mm"
include "ltled.mm"
include "simprr.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "absdifled.mm"
include "mpbir2and.mm"
include "jca.mm"
include "ex.mm"
include "sylbid.mm"
include "mpd.mm"

theorem aaliou3lem7
  let cA: class A
  let cF: class F
  let cH: class H
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume aaliou3lem.c: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )
  assume aaliou3lem.d: |- L = sum_ b e. NN ( F ` b )
  assume aaliou3lem.e: |- H = ( c e. NN |-> sum_ b e. ( 1 ... c ) ( F ` b ) )

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint F b
  disjoint F c
  disjoint L c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a d
  disjoint a e
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint F d
  disjoint F e
  disjoint L d
  disjoint L e
  disjoint L f
  disjoint c f
  disjoint d f
  disjoint e f
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint A d
  disjoint A e
  assert |- ( A e. NN -> ( ( H ` A ) =/= L /\ ( abs ` ( L - ( H ` A ) ) ) <_ ( 2 x. ( 2 ^ -u ( ! ` ( A + 1 ) ) ) ) ) )

  proof
    cA
    cn
    wcel
    #
    cA
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    vb
    csu
    #
    crp
    wcel
    #
    @5
    c2
    c2
    @1
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    cA
    cH
    cfv
    #
    cL
    wne
    #
    cL
    @13
    cmin
    co
    #
    cabs
    cfv
    @10
    cle
    wbr
    #
    wa
    #
    @0
    @1
    cn
    wcel
    #
    caddc
    cF
    @1
    cseq
    cli
    cdm
    #
    wcel
    #
    @6
    @11
    w3a
    @12
    cA
    peano2nn
    #
    @1
    cF
    vc
    @2
    @9
    c1
    c2
    cdiv
    co
    #
    vc
    cv
    #
    @1
    cmin
    co
    cexp
    co
    cmul
    co
    cmpt
    #
    va
    vb
    vc
    @24
    eqid
    aaliou3lem.c
    aaliou3lem3
    #
    @20
    @6
    @11
    3simpc
    3syl
    @0
    @12
    @15
    crp
    wcel
    #
    @15
    @10
    cle
    wbr
    #
    wa
    #
    @17
    @0
    @5
    @15
    wceq
    #
    @12
    @28
    wb
    @0
    @15
    @5
    @0
    @15
    @5
    wceq
    @13
    @5
    caddc
    co
    #
    cL
    wceq
    @0
    @30
    cn
    @4
    vb
    csu
    #
    cL
    @0
    c1
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    vb
    csu
    #
    @5
    caddc
    co
    c1
    cA
    cfz
    co
    #
    @4
    vb
    csu
    #
    @5
    caddc
    co
    @31
    @30
    @0
    @34
    @36
    @5
    caddc
    @0
    @33
    @35
    @4
    vb
    @0
    @32
    cA
    c1
    cfz
    @0
    cA
    cc
    wcel
    c1
    cc
    wcel
    @32
    cA
    wceq
    cA
    nncn
    ax-1cn
    cA
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    @0
    @4
    vb
    cF
    c1
    @1
    @2
    cn
    nnuz
    @2
    eqid
    @21
    @0
    @3
    cn
    wcel
    #
    wa
    @4
    eqidd
    @37
    @4
    cc
    wcel
    @0
    @37
    @4
    c2
    @3
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cc
    va
    @3
    c2
    va
    cv
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    @40
    cn
    cF
    va
    vb
    weq
    #
    @43
    @39
    c2
    cexp
    @44
    @42
    @38
    @41
    @3
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.c
    c2
    @39
    cexp
    ovex
    fvmpt
    @37
    @40
    @37
    c2
    crp
    wcel
    #
    @39
    cz
    wcel
    @40
    crp
    wcel
    2rp
    @37
    @38
    @37
    @38
    @37
    @3
    cn0
    wcel
    @38
    cn
    wcel
    @3
    nnnn0
    @3
    faccl
    syl
    nnzd
    znegcld
    c2
    @39
    rpexpcl
    sylancr
    rpcnd
    eqeltrd
    adantl
    c1
    cn
    wcel
    #
    caddc
    cF
    c1
    cseq
    @19
    wcel
    #
    @0
    1nn
    @46
    @47
    c1
    cuz
    cfv
    #
    @4
    vb
    csu
    #
    crp
    wcel
    @49
    c2
    c2
    c1
    cfa
    cfv
    cneg
    cexp
    co
    #
    cmul
    co
    cle
    wbr
    c1
    cF
    vc
    @48
    @50
    @22
    @23
    c1
    cmin
    co
    cexp
    co
    cmul
    co
    cmpt
    #
    va
    vb
    vc
    @51
    eqid
    aaliou3lem.c
    aaliou3lem3
    simp1d
    mp1i
    isumsplit
    @0
    @13
    @36
    @5
    caddc
    vc
    cA
    c1
    @23
    cfz
    co
    #
    @4
    vb
    csu
    @36
    cn
    cH
    @23
    cA
    wceq
    @52
    @35
    @4
    vb
    @23
    cA
    c1
    cfz
    oveq2
    sumeq1d
    aaliou3lem.e
    @35
    @4
    vb
    sumex
    fvmpt
    oveq1d
    3eqtr4rd
    aaliou3lem.d
    syl6eqr
    @0
    cL
    @13
    @5
    cL
    cc
    wcel
    @0
    cL
    cF
    cH
    cL
    va
    vb
    vc
    aaliou3lem.c
    aaliou3lem.d
    aaliou3lem.e
    aaliou3lem4
    #
    recni
    a1i
    @0
    @13
    cA
    cF
    cH
    cL
    va
    vb
    vc
    aaliou3lem.c
    aaliou3lem.d
    aaliou3lem.e
    aaliou3lem5
    #
    recnd
    @0
    @5
    @0
    @18
    @6
    @21
    @18
    @20
    @6
    @11
    @25
    simp2d
    syl
    rpcnd
    subaddd
    mpbird
    eqcomd
    @29
    @6
    @26
    @11
    @27
    @5
    @15
    crp
    eleq1
    @5
    @15
    @10
    cle
    breq1
    anbi12d
    syl
    @0
    @28
    @17
    @0
    @28
    wa
    #
    @14
    @16
    @55
    @13
    cL
    @0
    @13
    cr
    wcel
    #
    @28
    @54
    adantr
    #
    @55
    @13
    cL
    clt
    wbr
    #
    @26
    @0
    @26
    @27
    simprl
    @55
    @56
    cL
    cr
    wcel
    #
    @58
    @26
    wb
    @57
    @53
    @13
    cL
    difrp
    sylancl
    mpbird
    #
    ltned
    @55
    @16
    @13
    @10
    cmin
    co
    #
    cL
    cle
    wbr
    cL
    @13
    @10
    caddc
    co
    cle
    wbr
    #
    @55
    @61
    cL
    @55
    @13
    @10
    @57
    @55
    @10
    @0
    @10
    crp
    wcel
    #
    @28
    @0
    @45
    @9
    crp
    wcel
    #
    @63
    2rp
    @0
    @45
    @8
    cz
    wcel
    @64
    2rp
    @0
    @7
    @0
    @7
    @0
    @18
    @1
    cn0
    wcel
    @7
    cn
    wcel
    @21
    @1
    nnnn0
    @1
    faccl
    3syl
    nnzd
    znegcld
    c2
    @8
    rpexpcl
    sylancr
    c2
    @9
    rpmulcl
    sylancr
    adantr
    #
    rpred
    #
    resubcld
    #
    @59
    @55
    @53
    a1i
    #
    @55
    @61
    @13
    cL
    @67
    @57
    @68
    @55
    @13
    @10
    @57
    @65
    ltsubrpd
    @60
    lttrd
    ltled
    @55
    @27
    @62
    @0
    @26
    @27
    simprr
    @55
    cL
    @13
    @10
    @68
    @57
    @66
    lesubadd2d
    mpbid
    @55
    cL
    @13
    @10
    @68
    @57
    @66
    absdifled
    mpbir2and
    jca
    ex
    sylbid
    mpd
end
