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
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "cmin.mm"
include "cabs.mm"
include "cdiv.mm"
include "irrapxlem1.mm"
include "caddc.mm"
include "cr.mm"
include "nnre.mm"
include "ad3antlr.mm"
include "rpre.mm"
include "ad3antrrr.mm"
include "elfzelz.mm"
include "zred.mm"
include "ad2antlr.mm"
include "remulcld.mm"
include "1rp.mm"
include "a1i.mm"
include "modcld.mm"
include "intfrac.mm"
include "syl.mm"
include "adantl.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "flcld.mm"
include "zcnd.mm"
include "recnd.mm"
include "pnpcand.mm"
include "cico.mm"
include "0red.mm"
include "1red.mm"
include "modelico.mm"
include "sylancl.mm"
include "icodiamlt.mm"
include "syl22anc.mm"
include "1m0e1.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "wb.mm"
include "resubcld.mm"
include "abscld.mm"
include "nngt0.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "cle.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "eqcomd.mm"
include "absmuld.mm"
include "subdid.mm"
include "3eqtr2d.mm"
include "recidd.mm"
include "breq12d.mm"
include "bitrd.mm"
include "sylibrd.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"

theorem irrapxlem2
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
  assert |- ( ( A e. RR+ /\ B e. NN ) -> E. x e. ( 0 ... B ) E. y e. ( 0 ... B ) ( x < y /\ ( abs ` ( ( ( A x. x ) mod 1 ) - ( ( A x. y ) mod 1 ) ) ) < ( 1 / B ) ) )

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
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    cB
    cA
    @3
    cmul
    co
    #
    c1
    cmo
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cA
    @4
    cmul
    co
    #
    c1
    cmo
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cc0
    cB
    cfz
    co
    #
    wrex
    #
    vx
    @16
    wrex
    @5
    @7
    @11
    cmin
    co
    #
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
    vy
    @16
    wrex
    #
    vx
    @16
    wrex
    vx
    vy
    cA
    cB
    irrapxlem1
    @2
    @17
    @23
    vx
    @16
    @2
    @3
    @16
    wcel
    #
    wa
    #
    @15
    @22
    vy
    @16
    @25
    @4
    @16
    wcel
    #
    wa
    #
    @14
    @21
    @5
    @27
    @14
    @8
    @12
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    @21
    @27
    @14
    @30
    @27
    @14
    wa
    #
    @29
    @9
    @8
    c1
    cmo
    co
    #
    caddc
    co
    #
    @13
    @12
    c1
    cmo
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    @27
    @29
    @37
    wceq
    @14
    @27
    @28
    @36
    cabs
    @27
    @8
    @33
    @12
    @35
    cmin
    @27
    @8
    cr
    wcel
    #
    @8
    @33
    wceq
    @27
    cB
    @7
    @1
    cB
    cr
    wcel
    #
    @0
    @24
    @26
    cB
    nnre
    ad3antlr
    #
    @27
    @6
    c1
    @27
    cA
    @3
    @0
    cA
    cr
    wcel
    @1
    @24
    @26
    cA
    rpre
    ad3antrrr
    #
    @24
    @3
    cr
    wcel
    @2
    @26
    @24
    @3
    @3
    cc0
    cB
    elfzelz
    zred
    ad2antlr
    remulcld
    c1
    crp
    wcel
    #
    @27
    1rp
    a1i
    #
    modcld
    #
    remulcld
    #
    @8
    intfrac
    syl
    @27
    @12
    cr
    wcel
    #
    @12
    @35
    wceq
    @27
    cB
    @11
    @40
    @27
    @10
    c1
    @27
    cA
    @4
    @41
    @26
    @4
    cr
    wcel
    @25
    @26
    @4
    @4
    cc0
    cB
    elfzelz
    zred
    adantl
    remulcld
    @43
    modcld
    #
    remulcld
    #
    @12
    intfrac
    syl
    oveq12d
    fveq2d
    adantr
    @31
    @37
    @13
    @32
    caddc
    co
    #
    @35
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    @31
    @36
    @50
    cabs
    @31
    @33
    @49
    @35
    cmin
    @31
    @9
    @13
    @32
    caddc
    @27
    @14
    simpr
    oveq1d
    oveq1d
    fveq2d
    @27
    @51
    c1
    clt
    wbr
    @14
    @27
    @51
    @32
    @34
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    clt
    @27
    @50
    @52
    cabs
    @27
    @13
    @32
    @34
    @27
    @13
    @27
    @12
    @48
    flcld
    zcnd
    @27
    @32
    @27
    @8
    c1
    @45
    @43
    modcld
    recnd
    @27
    @34
    @27
    @12
    c1
    @48
    @43
    modcld
    recnd
    pnpcand
    fveq2d
    @27
    @53
    c1
    cc0
    cmin
    co
    #
    c1
    clt
    @27
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @32
    cc0
    c1
    cico
    co
    #
    wcel
    #
    @34
    @55
    wcel
    #
    @53
    @54
    clt
    wbr
    @27
    0red
    @27
    1red
    @27
    @38
    @42
    @56
    @45
    1rp
    @8
    c1
    modelico
    sylancl
    @27
    @46
    @42
    @57
    @48
    1rp
    @12
    c1
    modelico
    sylancl
    cc0
    c1
    @32
    @34
    icodiamlt
    syl22anc
    1m0e1
    syl6breq
    eqbrtrd
    adantr
    eqbrtrd
    eqbrtrd
    ex
    @27
    @21
    cB
    @19
    cmul
    co
    #
    cB
    @20
    cmul
    co
    #
    clt
    wbr
    #
    @30
    @27
    @19
    cr
    wcel
    @20
    cr
    wcel
    @39
    cc0
    cB
    clt
    wbr
    #
    @21
    @60
    wb
    @27
    @18
    @27
    @18
    @27
    @7
    @11
    @44
    @47
    resubcld
    recnd
    #
    abscld
    @27
    cB
    @40
    @27
    cB
    @1
    @61
    @0
    @24
    @26
    cB
    nngt0
    ad3antlr
    #
    gt0ne0d
    #
    rereccld
    @40
    @63
    @19
    @20
    cB
    ltmul2
    syl112anc
    @27
    @58
    @29
    @59
    c1
    clt
    @27
    @58
    cB
    cabs
    cfv
    #
    @19
    cmul
    co
    cB
    @18
    cmul
    co
    #
    cabs
    cfv
    @29
    @27
    cB
    @65
    @19
    cmul
    @27
    @65
    cB
    @27
    cB
    @40
    @1
    cc0
    cB
    cle
    wbr
    @0
    @24
    @26
    @1
    cB
    cB
    nnnn0
    nn0ge0d
    ad3antlr
    absidd
    eqcomd
    oveq1d
    @27
    cB
    @18
    @27
    cB
    @40
    recnd
    #
    @62
    absmuld
    @27
    @66
    @28
    cabs
    @27
    cB
    @7
    @11
    @67
    @27
    @7
    @44
    recnd
    @27
    @11
    @47
    recnd
    subdid
    fveq2d
    3eqtr2d
    @27
    cB
    @67
    @64
    recidd
    breq12d
    bitrd
    sylibrd
    anim2d
    reximdva
    reximdva
    mpd
end
