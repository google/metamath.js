include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "c4.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "2exp4.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "fac4.mm"
include "breq12d.mm"
include "cz.mm"
include "wcel.mm"
include "1nn0.mm"
include "2nn0.mm"
include "6nn0.mm"
include "4nn0.mm"
include "6lt10.mm"
include "1lt2.mm"
include "decltc.mm"
include "a1i.mm"
include "cuz.mm"
include "wa.mm"
include "cmul.mm"
include "cn.mm"
include "2nn.mm"
include "4nn.mm"
include "simpl.mm"
include "eluznn.mm"
include "sylancr.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "cr.mm"
include "2re.mm"
include "remulcld.mm"
include "faccld.mm"
include "1red.mm"
include "readdcld.mm"
include "crp.mm"
include "2rp.mm"
include "simpr.mm"
include "ltmul1dd.mm"
include "nn0ge0d.mm"
include "cle.mm"
include "df-2.mm"
include "nnge1d.mm"
include "leadd1dd.mm"
include "syl5eqbr.mm"
include "lemul2ad.mm"
include "ltletrd.mm"
include "2cnd.mm"
include "expp1d.mm"
include "cn0.mm"
include "facp1.mm"
include "syl.mm"
include "3brtr4d.mm"
include "ex.mm"
include "uzind4.mm"

theorem 2expltfac
  let cN: class N
  let vn: setvar n
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` 4 ) -> ( 2 ^ N ) < ( ! ` N ) )

  proof
    c2
    vx
    cv
    #
    cexp
    co
    #
    @0
    cfa
    cfv
    #
    clt
    wbr
    c1
    c6
    cdc
    #
    c2
    c4
    cdc
    #
    clt
    wbr
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    @6
    cfa
    cfv
    #
    clt
    wbr
    #
    c2
    @6
    c1
    caddc
    co
    #
    cexp
    co
    #
    @10
    cfa
    cfv
    #
    clt
    wbr
    #
    c2
    cN
    cexp
    co
    #
    cN
    cfa
    cfv
    #
    clt
    wbr
    vx
    vn
    c4
    cN
    @0
    c4
    wceq
    #
    @1
    @3
    @2
    @4
    clt
    @16
    @1
    c2
    c4
    cexp
    co
    @3
    @0
    c4
    c2
    cexp
    oveq2
    2exp4
    syl6eq
    @16
    @2
    c4
    cfa
    cfv
    @4
    @0
    c4
    cfa
    fveq2
    fac4
    syl6eq
    breq12d
    @0
    @6
    wceq
    @1
    @7
    @2
    @8
    clt
    @0
    @6
    c2
    cexp
    oveq2
    @0
    @6
    cfa
    fveq2
    breq12d
    @0
    @10
    wceq
    @1
    @11
    @2
    @12
    clt
    @0
    @10
    c2
    cexp
    oveq2
    @0
    @10
    cfa
    fveq2
    breq12d
    @0
    cN
    wceq
    @1
    @14
    @2
    @15
    clt
    @0
    cN
    c2
    cexp
    oveq2
    @0
    cN
    cfa
    fveq2
    breq12d
    @5
    c4
    cz
    wcel
    c1
    c2
    c6
    c4
    1nn0
    2nn0
    6nn0
    4nn0
    6lt10
    1lt2
    decltc
    a1i
    @6
    c4
    cuz
    cfv
    wcel
    #
    @9
    @13
    @17
    @9
    wa
    #
    @7
    c2
    cmul
    co
    #
    @8
    @10
    cmul
    co
    #
    @11
    @12
    clt
    @18
    @19
    @8
    c2
    cmul
    co
    @20
    @18
    @7
    c2
    @18
    @7
    @18
    c2
    @6
    c2
    cn
    wcel
    @18
    2nn
    a1i
    @18
    @6
    @18
    c4
    cn
    wcel
    @17
    @6
    cn
    wcel
    4nn
    @17
    @9
    simpl
    @6
    c4
    eluznn
    sylancr
    #
    nnnn0d
    #
    nnexpcld
    nnred
    #
    c2
    cr
    wcel
    @18
    2re
    a1i
    #
    remulcld
    @18
    @8
    c2
    @18
    @8
    @18
    @6
    @22
    faccld
    #
    nnred
    #
    @24
    remulcld
    @18
    @8
    @10
    @26
    @18
    @6
    c1
    @18
    @6
    @21
    nnred
    #
    @18
    1red
    #
    readdcld
    #
    remulcld
    @18
    @7
    @8
    c2
    @23
    @26
    c2
    crp
    wcel
    @18
    2rp
    a1i
    @17
    @9
    simpr
    ltmul1dd
    @18
    c2
    @10
    @8
    @24
    @29
    @26
    @18
    @8
    @18
    @8
    @25
    nnnn0d
    nn0ge0d
    @18
    c2
    c1
    c1
    caddc
    co
    @10
    cle
    df-2
    @18
    c1
    @6
    c1
    @28
    @27
    @28
    @18
    @6
    @21
    nnge1d
    leadd1dd
    syl5eqbr
    lemul2ad
    ltletrd
    @18
    c2
    @6
    @18
    2cnd
    @22
    expp1d
    @18
    @6
    cn0
    wcel
    @12
    @20
    wceq
    @22
    @6
    facp1
    syl
    3brtr4d
    ex
    uzind4
end
