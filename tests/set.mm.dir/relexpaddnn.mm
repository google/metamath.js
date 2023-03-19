include "cn.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "ccom.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "oveq2.mm"
include "coeq1d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "relexp1g.mm"
include "adantl.mm"
include "relexpsucnnl.mm"
include "ancoms.mm"
include "simpl.mm"
include "nncnd.mm"
include "1cnd.mm"
include "addcomd.mm"
include "3eqtr2d.mm"
include "w3a.mm"
include "simp2r.mm"
include "simp1.mm"
include "syl2anc.mm"
include "coass.mm"
include "syl6eq.mm"
include "simp3.mm"
include "coeq2d.mm"
include "cc.mm"
include "3ad2ant2.mm"
include "add32d.mm"
include "nnaddcld.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "3impib.mm"

theorem relexpaddnn
  let cR: class R
  let cM: class M
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vk: setvar k


  assert |- ( ( N e. NN /\ M e. NN /\ R e. V ) -> ( ( R ^r N ) o. ( R ^r M ) ) = ( R ^r ( N + M ) ) )

  proof
    cN
    cn
    wcel
    cM
    cn
    wcel
    #
    cR
    cV
    wcel
    #
    cR
    cN
    crelexp
    co
    #
    cR
    cM
    crelexp
    co
    #
    ccom
    #
    cR
    cN
    cM
    caddc
    co
    #
    crelexp
    co
    #
    wceq
    #
    @0
    @1
    wa
    #
    cR
    vn
    cv
    #
    crelexp
    co
    #
    @3
    ccom
    #
    cR
    @9
    cM
    caddc
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @8
    cR
    c1
    crelexp
    co
    #
    @3
    ccom
    #
    cR
    c1
    cM
    caddc
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @8
    cR
    vk
    cv
    #
    crelexp
    co
    #
    @3
    ccom
    #
    cR
    @20
    cM
    caddc
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @8
    cR
    @20
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @3
    ccom
    #
    cR
    @26
    cM
    caddc
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @8
    @7
    wi
    vn
    vk
    cN
    @9
    c1
    wceq
    #
    @14
    @19
    @8
    @32
    @11
    @16
    @13
    @18
    @32
    @10
    @15
    @3
    @9
    c1
    cR
    crelexp
    oveq2
    coeq1d
    @32
    @12
    @17
    cR
    crelexp
    @9
    c1
    cM
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi2d
    vn
    vk
    weq
    #
    @14
    @25
    @8
    @33
    @11
    @22
    @13
    @24
    @33
    @10
    @21
    @3
    @9
    @20
    cR
    crelexp
    oveq2
    coeq1d
    @33
    @12
    @23
    cR
    crelexp
    @9
    @20
    cM
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi2d
    @9
    @26
    wceq
    #
    @14
    @31
    @8
    @34
    @11
    @28
    @13
    @30
    @34
    @10
    @27
    @3
    @9
    @26
    cR
    crelexp
    oveq2
    coeq1d
    @34
    @12
    @29
    cR
    crelexp
    @9
    @26
    cM
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @14
    @7
    @8
    @35
    @11
    @4
    @13
    @6
    @35
    @10
    @2
    @3
    @9
    cN
    cR
    crelexp
    oveq2
    coeq1d
    @35
    @12
    @5
    cR
    crelexp
    @9
    cN
    cM
    caddc
    oveq1
    oveq2d
    eqeq12d
    imbi2d
    @8
    @16
    cR
    @3
    ccom
    #
    cR
    cM
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @18
    @8
    @15
    cR
    @3
    @1
    @15
    cR
    wceq
    @0
    cR
    cV
    relexp1g
    adantl
    coeq1d
    @1
    @0
    @38
    @36
    wceq
    cR
    cM
    cV
    relexpsucnnl
    ancoms
    @8
    @37
    @17
    cR
    crelexp
    @8
    cM
    c1
    @8
    cM
    @0
    @1
    simpl
    #
    nncnd
    #
    @8
    1cnd
    addcomd
    oveq2d
    3eqtr2d
    @20
    cn
    wcel
    #
    @8
    @25
    @31
    @41
    @8
    @25
    @31
    @41
    @8
    @25
    w3a
    #
    @28
    cR
    @22
    ccom
    #
    cR
    @24
    ccom
    #
    @30
    @42
    @28
    cR
    @21
    ccom
    #
    @3
    ccom
    @43
    @42
    @27
    @45
    @3
    @42
    @1
    @41
    @27
    @45
    wceq
    @41
    @0
    @1
    @25
    simp2r
    #
    @41
    @8
    @25
    simp1
    #
    cR
    @20
    cV
    relexpsucnnl
    syl2anc
    coeq1d
    cR
    @21
    @3
    coass
    syl6eq
    @42
    @22
    @24
    cR
    @41
    @8
    @25
    simp3
    coeq2d
    @42
    @30
    cR
    @23
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @44
    @42
    @29
    @48
    cR
    crelexp
    @42
    @20
    c1
    cM
    @42
    @20
    @47
    nncnd
    @42
    1cnd
    @8
    @41
    cM
    cc
    wcel
    @25
    @40
    3ad2ant2
    add32d
    oveq2d
    @42
    @1
    @23
    cn
    wcel
    @49
    @44
    wceq
    @46
    @42
    @20
    cM
    @47
    @8
    @41
    @0
    @25
    @39
    3ad2ant2
    nnaddcld
    cR
    @23
    cV
    relexpsucnnl
    syl2anc
    eqtr2d
    3eqtrd
    3exp
    a2d
    nnind
    3impib
end
