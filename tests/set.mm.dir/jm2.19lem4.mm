include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "crmy.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "caddc.mm"
include "wb.mm"
include "cr.mm"
include "cn0.mm"
include "cneg.mm"
include "wo.mm"
include "elznn0.mm"
include "wi.mm"
include "jm2.19lem3.mm"
include "3expia.mm"
include "adantr.mm"
include "simplll.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "nn0z.mm"
include "adantl.mm"
include "cc.mm"
include "simplr.mm"
include "recnd.mm"
include "znegclb.mm"
include "syl.mm"
include "mpbird.mm"
include "zmulcld.mm"
include "zaddcld.mm"
include "simpr.mm"
include "syl121anc.mm"
include "cmin.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "mulneg1d.mm"
include "oveq2d.mm"
include "ad2antll.mm"
include "mulcld.mm"
include "addcld.mm"
include "negsubd.mm"
include "pncand.mm"
include "3eqtrd.mm"
include "breq2d.mm"
include "bitr2d.mm"
include "ex.mm"
include "jaod.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem jm2.19lem4
  let cA: class A
  let cI: class I
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ ( M e. ZZ /\ N e. ZZ ) /\ I e. ZZ ) -> ( ( A rmY M ) || ( A rmY N ) <-> ( A rmY M ) || ( A rmY ( N + ( I x. M ) ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cI
    cz
    wcel
    #
    cA
    cM
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    cdvds
    wbr
    #
    @5
    cA
    cN
    cI
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    cdvds
    wbr
    #
    wb
    #
    @4
    cI
    cr
    wcel
    #
    cI
    cn0
    wcel
    #
    cI
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    @0
    @3
    wa
    #
    @11
    cI
    elznn0
    @17
    @12
    @16
    @11
    @17
    @12
    wa
    #
    @13
    @11
    @15
    @17
    @13
    @11
    wi
    @12
    @0
    @3
    @13
    @11
    cA
    cI
    cM
    cN
    jm2.19lem3
    3expia
    adantr
    @18
    @15
    @11
    @18
    @15
    wa
    #
    @10
    @5
    cA
    @9
    @14
    cM
    cmul
    co
    #
    caddc
    co
    #
    crmy
    co
    #
    cdvds
    wbr
    #
    @7
    @19
    @0
    @1
    @9
    cz
    wcel
    @15
    @10
    @23
    wb
    @0
    @3
    @12
    @15
    simplll
    @17
    @1
    @12
    @15
    @0
    @1
    @2
    simprl
    ad2antrr
    #
    @19
    cN
    @8
    @17
    @2
    @12
    @15
    @0
    @1
    @2
    simprr
    ad2antrr
    @19
    cI
    cM
    @19
    @4
    @14
    cz
    wcel
    #
    @15
    @25
    @18
    @14
    nn0z
    adantl
    @19
    cI
    cc
    wcel
    @4
    @25
    wb
    @19
    cI
    @17
    @12
    @15
    simplr
    recnd
    #
    cI
    znegclb
    syl
    mpbird
    @24
    zmulcld
    zaddcld
    @18
    @15
    simpr
    cA
    @14
    cM
    @9
    jm2.19lem3
    syl121anc
    @19
    @22
    @6
    @5
    cdvds
    @19
    @21
    cN
    cA
    crmy
    @19
    @21
    @9
    @8
    cneg
    #
    caddc
    co
    @9
    @8
    cmin
    co
    cN
    @19
    @20
    @27
    @9
    caddc
    @19
    cI
    cM
    @26
    @17
    cM
    cc
    wcel
    #
    @12
    @15
    @1
    @28
    @0
    @2
    cM
    zcn
    ad2antrl
    ad2antrr
    #
    mulneg1d
    oveq2d
    @19
    @9
    @8
    @19
    cN
    @8
    @17
    cN
    cc
    wcel
    #
    @12
    @15
    @2
    @30
    @0
    @1
    cN
    zcn
    ad2antll
    ad2antrr
    #
    @19
    cI
    cM
    @26
    @29
    mulcld
    #
    addcld
    @32
    negsubd
    @19
    cN
    @8
    @31
    @32
    pncand
    3eqtrd
    oveq2d
    breq2d
    bitr2d
    ex
    jaod
    expimpd
    syl5bi
    3impia
end
