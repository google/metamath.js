include "crp.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmo.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cdiv.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "cn0.mm"
include "irrapxlem2.mm"
include "cfl.mm"
include "cle.mm"
include "1m1e0.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad2antrl.mm"
include "zred.mm"
include "ad2antll.mm"
include "posdifd.mm"
include "biimpa.mm"
include "syl5eqbr.mm"
include "wb.mm"
include "1z.mm"
include "simplrr.mm"
include "syl.mm"
include "simplrl.mm"
include "zsubcld.mm"
include "zlem1lt.mm"
include "sylancr.mm"
include "mpbird.mm"
include "resubcld.mm"
include "0red.mm"
include "simpllr.mm"
include "nnred.mm"
include "elfzle1.mm"
include "lesub2dd.mm"
include "recnd.mm"
include "subid1d.mm"
include "elfzle2.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "a1i.mm"
include "nnzd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "adantrr.mm"
include "cuz.mm"
include "cr.mm"
include "rpre.mm"
include "ad3antrrr.mm"
include "remulcld.mm"
include "simpr.mm"
include "ltled.mm"
include "rpgt0.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "flword2.mm"
include "uznn0sub.mm"
include "subdid.mm"
include "oveq1d.mm"
include "flcld.mm"
include "zcnd.mm"
include "sub4d.mm"
include "wceq.mm"
include "modfrac.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "1rp.mm"
include "modcld.mm"
include "abssubd.mm"
include "eqtr2d.mm"
include "breq1d.mm"
include "biimpd.mm"
include "impr.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem irrapxlem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint b y
  disjoint B a
  disjoint B b
  assert |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 1 ... B ) E. y e. NN0 ( abs ` ( ( A x. x ) - y ) ) < ( 1 / B ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    clt
    wbr
    #
    cA
    @3
    cmul
    co
    #
    c1
    cmo
    co
    #
    cA
    @4
    cmul
    co
    #
    c1
    cmo
    co
    #
    cmin
    co
    cabs
    cfv
    #
    c1
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    wa
    #
    vb
    cc0
    cB
    cfz
    co
    #
    wrex
    va
    @14
    wrex
    cA
    vx
    cv
    #
    cmul
    co
    #
    vy
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    vy
    cn0
    wrex
    vx
    c1
    cB
    cfz
    co
    #
    wrex
    #
    va
    vb
    cA
    cB
    irrapxlem2
    @2
    @13
    @22
    va
    vb
    @14
    @14
    @2
    @3
    @14
    wcel
    #
    @4
    @14
    wcel
    #
    wa
    #
    wa
    #
    @13
    @22
    @26
    @13
    wa
    @4
    @3
    cmin
    co
    #
    @21
    wcel
    #
    @8
    cfl
    cfv
    #
    @6
    cfl
    cfv
    #
    cmin
    co
    #
    cn0
    wcel
    #
    cA
    @27
    cmul
    co
    #
    @31
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    @22
    @26
    @5
    @28
    @12
    @26
    @5
    wa
    #
    @28
    c1
    @27
    cle
    wbr
    #
    @27
    cB
    cle
    wbr
    #
    @37
    @38
    c1
    c1
    cmin
    co
    #
    @27
    clt
    wbr
    #
    @37
    @40
    cc0
    @27
    clt
    1m1e0
    @26
    @5
    cc0
    @27
    clt
    wbr
    @26
    @3
    @4
    @26
    @3
    @23
    @3
    cz
    wcel
    #
    @2
    @24
    @3
    cc0
    cB
    elfzelz
    #
    ad2antrl
    zred
    @26
    @4
    @24
    @4
    cz
    wcel
    #
    @2
    @23
    @4
    cc0
    cB
    elfzelz
    #
    ad2antll
    zred
    posdifd
    biimpa
    syl5eqbr
    @37
    c1
    cz
    wcel
    #
    @27
    cz
    wcel
    #
    @38
    @41
    wb
    1z
    @37
    @4
    @3
    @37
    @24
    @44
    @2
    @23
    @24
    @5
    simplrr
    #
    @45
    syl
    #
    @37
    @23
    @42
    @2
    @23
    @24
    @5
    simplrl
    #
    @43
    syl
    #
    zsubcld
    #
    c1
    @27
    zlem1lt
    sylancr
    mpbird
    @37
    @27
    @4
    cc0
    cmin
    co
    #
    cB
    @37
    @4
    @3
    @37
    @4
    @49
    zred
    #
    @37
    @3
    @51
    zred
    #
    resubcld
    @37
    @4
    cc0
    @54
    @37
    0red
    #
    resubcld
    @37
    cB
    @0
    @1
    @25
    @5
    simpllr
    #
    nnred
    @37
    cc0
    @3
    @4
    @56
    @55
    @54
    @37
    @23
    cc0
    @3
    cle
    wbr
    @50
    @3
    cc0
    cB
    elfzle1
    syl
    lesub2dd
    @37
    @53
    @4
    cB
    cle
    @37
    @4
    @37
    @4
    @54
    recnd
    #
    subid1d
    @37
    @24
    @4
    cB
    cle
    wbr
    @48
    @4
    cc0
    cB
    elfzle2
    syl
    eqbrtrd
    letrd
    @37
    @47
    @46
    cB
    cz
    wcel
    @28
    @38
    @39
    wa
    wb
    @52
    @46
    @37
    1z
    a1i
    @37
    cB
    @57
    nnzd
    @27
    c1
    cB
    elfz
    syl3anc
    mpbir2and
    adantrr
    @26
    @5
    @32
    @12
    @37
    @29
    @30
    cuz
    cfv
    wcel
    #
    @32
    @37
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @6
    @8
    cle
    wbr
    #
    @59
    @37
    cA
    @3
    @0
    cA
    cr
    wcel
    #
    @1
    @25
    @5
    cA
    rpre
    ad3antrrr
    #
    @55
    remulcld
    #
    @37
    cA
    @4
    @64
    @54
    remulcld
    #
    @37
    @3
    @4
    cle
    wbr
    #
    @62
    @37
    @3
    @4
    @55
    @54
    @26
    @5
    simpr
    ltled
    @37
    @3
    cr
    wcel
    @4
    cr
    wcel
    @63
    cc0
    cA
    clt
    wbr
    #
    @67
    @62
    wb
    @55
    @54
    @64
    @0
    @68
    @1
    @25
    @5
    cA
    rpgt0
    ad3antrrr
    @3
    @4
    cA
    lemul2
    syl112anc
    mpbid
    @6
    @8
    flword2
    syl3anc
    @30
    @29
    uznn0sub
    syl
    adantrr
    @26
    @5
    @12
    @36
    @37
    @12
    @36
    @37
    @10
    @35
    @11
    clt
    @37
    @35
    @9
    @7
    cmin
    co
    #
    cabs
    cfv
    @10
    @37
    @34
    @69
    cabs
    @37
    @34
    @8
    @6
    cmin
    co
    #
    @31
    cmin
    co
    @8
    @29
    cmin
    co
    #
    @6
    @30
    cmin
    co
    #
    cmin
    co
    @69
    @37
    @33
    @70
    @31
    cmin
    @37
    cA
    @4
    @3
    @37
    cA
    @64
    recnd
    @58
    @37
    @3
    @55
    recnd
    subdid
    oveq1d
    @37
    @8
    @6
    @29
    @30
    @37
    @8
    @66
    recnd
    @37
    @6
    @65
    recnd
    @37
    @29
    @37
    @8
    @66
    flcld
    zcnd
    @37
    @30
    @37
    @6
    @65
    flcld
    zcnd
    sub4d
    @37
    @71
    @9
    @72
    @7
    cmin
    @37
    @9
    @71
    @37
    @61
    @9
    @71
    wceq
    @66
    @8
    modfrac
    syl
    eqcomd
    @37
    @7
    @72
    @37
    @60
    @7
    @72
    wceq
    @65
    @6
    modfrac
    syl
    eqcomd
    oveq12d
    3eqtrd
    fveq2d
    @37
    @9
    @7
    @37
    @9
    @37
    @8
    c1
    @66
    c1
    crp
    wcel
    @37
    1rp
    a1i
    #
    modcld
    recnd
    @37
    @7
    @37
    @6
    c1
    @65
    @73
    modcld
    recnd
    abssubd
    eqtr2d
    breq1d
    biimpd
    impr
    @20
    @36
    @33
    @17
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    vx
    vy
    @27
    @31
    @21
    cn0
    @15
    @27
    wceq
    #
    @19
    @75
    @11
    clt
    @76
    @18
    @74
    cabs
    @76
    @16
    @33
    @17
    cmin
    @15
    @27
    cA
    cmul
    oveq2
    oveq1d
    fveq2d
    breq1d
    @17
    @31
    wceq
    #
    @75
    @35
    @11
    clt
    @77
    @74
    @34
    cabs
    @17
    @31
    @33
    cmin
    oveq2
    fveq2d
    breq1d
    rspc2ev
    syl3anc
    ex
    rexlimdvva
    mpd
end
