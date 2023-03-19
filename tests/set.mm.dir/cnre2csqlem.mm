include "cr.mm"
include "cxp.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cres.mm"
include "ccnv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cioo.mm"
include "cima.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "cvv.mm"
include "wss.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "elpreima.mm"
include "mp1i.mm"
include "simplbda.mm"
include "ex.mm"
include "wceq.mm"
include "simp2.mm"
include "fvres.mm"
include "syl.mm"
include "eleq1d.mm"
include "cxr.mm"
include "simp1.mm"
include "cv.mm"
include "fveq2.mm"
include "vtoclga.mm"
include "simp3.mm"
include "rpred.mm"
include "resubcld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp2d.mm"
include "simp3d.mm"
include "jca.mm"
include "sylbid.mm"
include "wi.mm"
include "absdiflt.mm"
include "biimprd.mm"
include "syl3anc.mm"
include "3syld.mm"
include "crn.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "vtocl2ga.mm"
include "ccom.mm"
include "fveq1i.mm"
include "fvco2.mm"
include "3eqtr3a.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "sylibrd.mm"

theorem cnre2csqlem
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  assume cnre2csqlem.1: |- ( G |` ( RR X. RR ) ) = ( H o. F )
  assume cnre2csqlem.2: |- F Fn ( RR X. RR )
  assume cnre2csqlem.3: |- G Fn _V
  assume cnre2csqlem.4: |- ( x e. ( RR X. RR ) -> ( G ` x ) e. RR )
  assume cnre2csqlem.5: |- ( ( x e. ran F /\ y e. ran F ) -> ( H ` ( x - y ) ) = ( ( H ` x ) - ( H ` y ) ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( X e. ( RR X. RR ) /\ Y e. ( RR X. RR ) /\ D e. RR+ ) -> ( Y e. ( `' ( G |` ( RR X. RR ) ) " ( ( ( G ` X ) - D ) (,) ( ( G ` X ) + D ) ) ) -> ( abs ` ( H ` ( ( F ` Y ) - ( F ` X ) ) ) ) < D ) )

  proof
    cX
    cr
    cr
    cxp
    #
    wcel
    #
    cY
    @0
    wcel
    #
    cD
    crp
    wcel
    #
    w3a
    #
    cY
    cG
    @0
    cres
    #
    ccnv
    cX
    cG
    cfv
    #
    cD
    cmin
    co
    #
    @6
    cD
    caddc
    co
    #
    cioo
    co
    #
    cima
    wcel
    #
    cY
    cG
    cfv
    #
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    cD
    clt
    wbr
    #
    cY
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cmin
    co
    #
    cH
    cfv
    #
    cabs
    cfv
    #
    cD
    clt
    wbr
    @4
    @10
    cY
    @5
    cfv
    #
    @9
    wcel
    #
    @7
    @11
    clt
    wbr
    #
    @11
    @8
    clt
    wbr
    #
    wa
    #
    @14
    @4
    @10
    @21
    @4
    @10
    @2
    @21
    @5
    @0
    wfn
    #
    @10
    @2
    @21
    wa
    wb
    @4
    cG
    cvv
    wfn
    @0
    cvv
    wss
    @25
    cnre2csqlem.3
    @0
    ssv
    cvv
    @0
    cG
    fnssres
    mp2an
    @0
    cY
    @9
    @5
    elpreima
    mp1i
    simplbda
    ex
    @4
    @21
    @11
    @9
    wcel
    #
    @24
    @4
    @20
    @11
    @9
    @4
    @2
    @20
    @11
    wceq
    @1
    @2
    @3
    simp2
    #
    cY
    @0
    cG
    fvres
    syl
    #
    eleq1d
    @4
    @26
    @24
    @4
    @26
    wa
    #
    @22
    @23
    @29
    @11
    cr
    wcel
    #
    @22
    @23
    @4
    @26
    @30
    @22
    @23
    w3a
    #
    @4
    @7
    cxr
    wcel
    @8
    cxr
    wcel
    @26
    @31
    wb
    @4
    @7
    @4
    @6
    cD
    @4
    @1
    @6
    cr
    wcel
    #
    @1
    @2
    @3
    simp1
    #
    vx
    cv
    #
    cG
    cfv
    #
    cr
    wcel
    #
    @32
    vx
    cX
    @0
    @34
    cX
    wceq
    @35
    @6
    cr
    @34
    cX
    cG
    fveq2
    eleq1d
    cnre2csqlem.4
    vtoclga
    syl
    #
    @4
    cD
    @1
    @2
    @3
    simp3
    rpred
    #
    resubcld
    rexrd
    @4
    @8
    @4
    @6
    cD
    @37
    @38
    readdcld
    rexrd
    @7
    @8
    @11
    elioo2
    syl2anc
    biimpa
    #
    simp2d
    @29
    @30
    @22
    @23
    @39
    simp3d
    jca
    ex
    sylbid
    @4
    @30
    @32
    cD
    cr
    wcel
    #
    @24
    @14
    wi
    @4
    @2
    @30
    @27
    @36
    @30
    vx
    cY
    @0
    @34
    cY
    wceq
    @35
    @11
    cr
    @34
    cY
    cG
    fveq2
    eleq1d
    cnre2csqlem.4
    vtoclga
    syl
    @37
    @38
    @30
    @32
    @40
    w3a
    @14
    @24
    @11
    @6
    cD
    absdiflt
    biimprd
    syl3anc
    3syld
    @4
    @19
    @13
    cD
    clt
    @4
    @18
    @12
    cabs
    @4
    @18
    @15
    cH
    cfv
    #
    @16
    cH
    cfv
    #
    cmin
    co
    #
    @12
    @4
    @15
    cF
    crn
    #
    wcel
    #
    @16
    @44
    wcel
    #
    @18
    @43
    wceq
    #
    @4
    cF
    @0
    wfn
    #
    @2
    @45
    cnre2csqlem.2
    @27
    @0
    cY
    cF
    fnfvelrn
    sylancr
    @4
    @48
    @1
    @46
    cnre2csqlem.2
    @33
    @0
    cX
    cF
    fnfvelrn
    sylancr
    @34
    vy
    cv
    #
    cmin
    co
    #
    cH
    cfv
    #
    @34
    cH
    cfv
    #
    @49
    cH
    cfv
    #
    cmin
    co
    #
    wceq
    @15
    @49
    cmin
    co
    #
    cH
    cfv
    #
    @41
    @53
    cmin
    co
    #
    wceq
    @47
    vx
    vy
    @15
    @16
    @44
    @44
    @34
    @15
    wceq
    #
    @51
    @56
    @54
    @57
    @58
    @50
    @55
    cH
    @34
    @15
    @49
    cmin
    oveq1
    fveq2d
    @58
    @52
    @41
    @53
    cmin
    @34
    @15
    cH
    fveq2
    oveq1d
    eqeq12d
    @49
    @16
    wceq
    #
    @56
    @18
    @57
    @43
    @59
    @55
    @17
    cH
    @49
    @16
    @15
    cmin
    oveq2
    fveq2d
    @59
    @53
    @42
    @41
    cmin
    @49
    @16
    cH
    fveq2
    oveq2d
    eqeq12d
    cnre2csqlem.5
    vtocl2ga
    syl2anc
    @4
    @11
    @41
    @6
    @42
    cmin
    @4
    @20
    cY
    cH
    cF
    ccom
    #
    cfv
    #
    @11
    @41
    cY
    @5
    @60
    cnre2csqlem.1
    fveq1i
    @28
    @4
    @48
    @2
    @61
    @41
    wceq
    cnre2csqlem.2
    @27
    @0
    cH
    cF
    cY
    fvco2
    sylancr
    3eqtr3a
    @4
    cX
    @5
    cfv
    #
    cX
    @60
    cfv
    #
    @6
    @42
    cX
    @5
    @60
    cnre2csqlem.1
    fveq1i
    @4
    @1
    @62
    @6
    wceq
    @33
    cX
    @0
    cG
    fvres
    syl
    @4
    @48
    @1
    @63
    @42
    wceq
    cnre2csqlem.2
    @33
    @0
    cH
    cF
    cX
    fvco2
    sylancr
    3eqtr3a
    oveq12d
    eqtr4d
    fveq2d
    breq1d
    sylibrd
end
