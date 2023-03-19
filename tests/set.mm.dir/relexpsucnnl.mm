include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crelexp.mm"
include "ccom.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "coeq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "relexp1g.mm"
include "coeq1d.mm"
include "1nn.mm"
include "relexpsucnnr.mm"
include "mpan2.mm"
include "3eqtr4d.mm"
include "wa.mm"
include "coeq1.mm"
include "coass.mm"
include "syl6eq.mm"
include "adantl.mm"
include "simpl.mm"
include "peano2nn.mm"
include "anim2i.mm"
include "3syl.mm"
include "adantr.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem relexpsucnnl
  let cR: class R
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vm: setvar m


  assert |- ( ( R e. V /\ N e. NN ) -> ( R ^r ( N + 1 ) ) = ( R o. ( R ^r N ) ) )

  proof
    cN
    cn
    wcel
    cR
    cV
    wcel
    #
    cR
    cN
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cR
    cN
    crelexp
    co
    #
    ccom
    #
    wceq
    #
    @0
    cR
    vn
    cv
    #
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cR
    @6
    crelexp
    co
    #
    ccom
    #
    wceq
    #
    wi
    @0
    cR
    c1
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cR
    c1
    crelexp
    co
    #
    ccom
    #
    wceq
    #
    wi
    @0
    cR
    vm
    cv
    #
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cR
    @17
    crelexp
    co
    #
    ccom
    #
    wceq
    #
    wi
    @0
    cR
    @18
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    @19
    ccom
    #
    wceq
    #
    wi
    @0
    @5
    wi
    vn
    vm
    cN
    @6
    c1
    wceq
    #
    @11
    @16
    @0
    @27
    @8
    @13
    @10
    @15
    @27
    @7
    @12
    cR
    crelexp
    @6
    c1
    c1
    caddc
    oveq1
    oveq2d
    @27
    @9
    @14
    cR
    @6
    c1
    cR
    crelexp
    oveq2
    coeq2d
    eqeq12d
    imbi2d
    vn
    vm
    weq
    #
    @11
    @22
    @0
    @28
    @8
    @19
    @10
    @21
    @28
    @7
    @18
    cR
    crelexp
    @6
    @17
    c1
    caddc
    oveq1
    oveq2d
    @28
    @9
    @20
    cR
    @6
    @17
    cR
    crelexp
    oveq2
    coeq2d
    eqeq12d
    imbi2d
    @6
    @18
    wceq
    #
    @11
    @26
    @0
    @29
    @8
    @24
    @10
    @25
    @29
    @7
    @23
    cR
    crelexp
    @6
    @18
    c1
    caddc
    oveq1
    oveq2d
    @29
    @9
    @19
    cR
    @6
    @18
    cR
    crelexp
    oveq2
    coeq2d
    eqeq12d
    imbi2d
    @6
    cN
    wceq
    #
    @11
    @5
    @0
    @30
    @8
    @2
    @10
    @4
    @30
    @7
    @1
    cR
    crelexp
    @6
    cN
    c1
    caddc
    oveq1
    oveq2d
    @30
    @9
    @3
    cR
    @6
    cN
    cR
    crelexp
    oveq2
    coeq2d
    eqeq12d
    imbi2d
    @0
    @14
    cR
    ccom
    #
    cR
    cR
    ccom
    @13
    @15
    @0
    @14
    cR
    cR
    cR
    cV
    relexp1g
    #
    coeq1d
    @0
    c1
    cn
    wcel
    @13
    @31
    wceq
    1nn
    cR
    c1
    cV
    relexpsucnnr
    mpan2
    @0
    @14
    cR
    cR
    @32
    coeq2d
    3eqtr4d
    @17
    cn
    wcel
    #
    @0
    @22
    @26
    @0
    @33
    @22
    @26
    wi
    @0
    @33
    wa
    #
    @22
    @26
    @34
    @22
    wa
    #
    @19
    cR
    ccom
    #
    cR
    @20
    cR
    ccom
    #
    ccom
    #
    @24
    @25
    @22
    @36
    @38
    wceq
    @34
    @22
    @36
    @21
    cR
    ccom
    @38
    @19
    @21
    cR
    coeq1
    cR
    @20
    cR
    coass
    syl6eq
    adantl
    @35
    @34
    @0
    @18
    cn
    wcel
    #
    wa
    @24
    @36
    wceq
    @34
    @22
    simpl
    @33
    @39
    @0
    @17
    peano2nn
    anim2i
    cR
    @18
    cV
    relexpsucnnr
    3syl
    @35
    @19
    @37
    cR
    @34
    @19
    @37
    wceq
    @22
    cR
    @17
    cV
    relexpsucnnr
    adantr
    coeq2d
    3eqtr4d
    ex
    expcom
    a2d
    nnind
    impcom
end
