include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cn.mm"
include "crelexp.mm"
include "wi.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "ovexd.mm"
include "relexp1d.mm"
include "cr.mm"
include "simp1.mm"
include "nnre.mm"
include "ax-1rid.mm"
include "3syl.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "ccom.mm"
include "cvv.mm"
include "ovex.mm"
include "relexpsucnnr.mm"
include "sylancr.mm"
include "simp3.mm"
include "coeq1d.mm"
include "simp21.mm"
include "nnmulcld.mm"
include "simp22.mm"
include "relexpaddnn.mm"
include "syl3anc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "adddid.mm"
include "mulid1d.mm"
include "eqtr2d.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "3expd.mm"
include "impcom.mm"
include "impd.mm"
include "simplr.mm"

theorem relexpmulnn
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( R e. V /\ I = ( J x. K ) ) /\ ( J e. NN /\ K e. NN ) ) -> ( ( R ^r J ) ^r K ) = ( R ^r I ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cJ
    cK
    cmul
    co
    #
    wceq
    #
    wa
    #
    cJ
    cn
    wcel
    #
    cK
    cn
    wcel
    #
    wa
    #
    wa
    #
    cR
    cJ
    crelexp
    co
    #
    cK
    crelexp
    co
    #
    cR
    @1
    crelexp
    co
    #
    cR
    cI
    crelexp
    co
    @6
    @3
    @9
    @10
    wceq
    #
    @6
    @0
    @2
    @11
    @5
    @4
    @0
    @2
    @11
    wi
    wi
    @5
    @4
    @0
    @2
    @11
    @4
    @0
    @2
    w3a
    #
    @8
    vx
    cv
    #
    crelexp
    co
    #
    cR
    cJ
    @13
    cmul
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @12
    @8
    c1
    crelexp
    co
    #
    cR
    cJ
    c1
    cmul
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @12
    @8
    vy
    cv
    #
    crelexp
    co
    #
    cR
    cJ
    @22
    cmul
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @12
    @8
    @22
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cJ
    @27
    cmul
    co
    #
    crelexp
    co
    #
    wceq
    #
    wi
    @12
    @11
    wi
    vx
    vy
    cK
    @13
    c1
    wceq
    #
    @17
    @21
    @12
    @32
    @14
    @18
    @16
    @20
    @13
    c1
    @8
    crelexp
    oveq2
    @32
    @15
    @19
    cR
    crelexp
    @13
    c1
    cJ
    cmul
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @17
    @26
    @12
    @33
    @14
    @23
    @16
    @25
    @13
    @22
    @8
    crelexp
    oveq2
    @33
    @15
    @24
    cR
    crelexp
    @13
    @22
    cJ
    cmul
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @13
    @27
    wceq
    #
    @17
    @31
    @12
    @34
    @14
    @28
    @16
    @30
    @13
    @27
    @8
    crelexp
    oveq2
    @34
    @15
    @29
    cR
    crelexp
    @13
    @27
    cJ
    cmul
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @13
    cK
    wceq
    #
    @17
    @11
    @12
    @35
    @14
    @9
    @16
    @10
    @13
    cK
    @8
    crelexp
    oveq2
    @35
    @15
    @1
    cR
    crelexp
    @13
    cK
    cJ
    cmul
    oveq2
    oveq2d
    eqeq12d
    imbi2d
    @12
    @18
    @8
    @20
    @12
    @8
    @12
    cR
    cJ
    crelexp
    ovexd
    relexp1d
    @12
    cJ
    @19
    cR
    crelexp
    @12
    @19
    cJ
    @12
    @4
    cJ
    cr
    wcel
    @19
    cJ
    wceq
    @4
    @0
    @2
    simp1
    cJ
    nnre
    cJ
    ax-1rid
    3syl
    eqcomd
    oveq2d
    eqtrd
    @22
    cn
    wcel
    #
    @12
    @26
    @31
    @36
    @12
    @26
    @31
    @36
    @12
    @26
    w3a
    #
    @28
    @23
    @8
    ccom
    #
    @30
    @37
    @8
    cvv
    wcel
    @36
    @28
    @38
    wceq
    cR
    cJ
    crelexp
    ovex
    @36
    @12
    @26
    simp1
    #
    @8
    @22
    cvv
    relexpsucnnr
    sylancr
    @37
    @38
    cR
    @24
    cJ
    caddc
    co
    #
    crelexp
    co
    #
    @30
    @37
    @38
    @25
    @8
    ccom
    #
    @41
    @37
    @23
    @25
    @8
    @36
    @12
    @26
    simp3
    coeq1d
    @37
    @24
    cn
    wcel
    @4
    @0
    @42
    @41
    wceq
    @37
    cJ
    @22
    @36
    @4
    @0
    @2
    @26
    simp21
    #
    @39
    nnmulcld
    @43
    @36
    @4
    @0
    @2
    @26
    simp22
    cR
    cJ
    @24
    cV
    relexpaddnn
    syl3anc
    eqtrd
    @37
    @40
    @29
    cR
    crelexp
    @37
    @29
    @24
    @19
    caddc
    co
    @40
    @37
    cJ
    @22
    c1
    @37
    cJ
    @43
    nncnd
    #
    @37
    @22
    @39
    nncnd
    @37
    1cnd
    adddid
    @37
    @19
    cJ
    @24
    caddc
    @37
    cJ
    @44
    mulid1d
    oveq2d
    eqtr2d
    oveq2d
    eqtrd
    eqtrd
    3exp
    a2d
    nnind
    3expd
    impcom
    impd
    impcom
    @7
    @1
    cI
    cR
    crelexp
    @7
    cI
    @1
    @0
    @2
    @6
    simplr
    eqcomd
    oveq2d
    eqtrd
end
