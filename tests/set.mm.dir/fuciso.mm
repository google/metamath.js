include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "wral.mm"
include "wa.mm"
include "cfunc.mm"
include "fucbas.mm"
include "fuchom.mm"
include "ccat.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "fuccat.mm"
include "isohom.mm"
include "sselda.mm"
include "cbs.mm"
include "cinv.mm"
include "eqid.mm"
include "ad2antrr.mm"
include "wf.mm"
include "c2nd.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "w3a.mm"
include "cdm.mm"
include "isoval.mm"
include "eleq2d.mm"
include "wfun.mm"
include "wb.mm"
include "invfun.mm"
include "funfvbrb.mm"
include "bitrd.mm"
include "biimpa.mm"
include "fucinv.mm"
include "mpbid.mm"
include "simp3d.mm"
include "r19.21bi.mm"
include "inviso1.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cmpt.mm"
include "simprl.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "eleqtrd.mm"
include "invfuc.mm"
include "impbida.mm"

theorem fuciso
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cN: class N
  let vy: setvar y
  let vf: setvar f
  let vz: setvar z
  let cV: class V
  let cU: class U
  let cX: class X
  assume fuciso.q: |- Q = ( C FuncCat D )
  assume fuciso.b: |- B = ( Base ` C )
  assume fuciso.n: |- N = ( C Nat D )
  assume fuciso.f: |- ( ph -> F e. ( C Func D ) )
  assume fuciso.g: |- ( ph -> G e. ( C Func D ) )
  assume fuciso.i: |- I = ( Iso ` Q )
  assume fuciso.j: |- J = ( Iso ` D )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint I x
  disjoint F x
  disjoint G x
  disjoint J x
  disjoint N x
  disjoint ph x
  disjoint Q x
  disjoint x y
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C y
  disjoint C z
  disjoint D f
  disjoint D y
  disjoint D z
  disjoint I y
  disjoint F f
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint J y
  disjoint N y
  disjoint V f
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint Q y
  disjoint U x
  disjoint U y
  disjoint X f
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( A e. ( F I G ) <-> ( A e. ( F N G ) /\ A. x e. B ( A ` x ) e. ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) ) ) )

  proof
    wph
    cA
    cF
    cG
    cI
    co
    #
    wcel
    #
    cA
    cF
    cG
    cN
    co
    #
    wcel
    #
    vx
    cv
    #
    cA
    cfv
    #
    @4
    cF
    c1st
    cfv
    #
    cfv
    #
    @4
    cG
    c1st
    cfv
    #
    cfv
    #
    cJ
    co
    #
    wcel
    #
    vx
    cB
    wral
    #
    wa
    #
    wph
    @1
    wa
    #
    @3
    @12
    wph
    @0
    @2
    cA
    wph
    cC
    cD
    cfunc
    co
    #
    cQ
    cN
    cI
    cF
    cG
    cC
    cD
    cQ
    fuciso.q
    fucbas
    #
    cC
    cD
    cQ
    cN
    fuciso.q
    fuciso.n
    fuchom
    fuciso.i
    wph
    cC
    cD
    cQ
    fuciso.q
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    wph
    cF
    @15
    wcel
    #
    @17
    @18
    wa
    fuciso.f
    cC
    cD
    cF
    funcrcl
    syl
    #
    simpld
    wph
    @17
    @18
    @20
    simprd
    #
    fuccat
    #
    fuciso.f
    fuciso.g
    isohom
    sselda
    @14
    @11
    vx
    cB
    @14
    @4
    cB
    wcel
    #
    wa
    cD
    cbs
    cfv
    #
    cD
    @5
    @4
    cA
    cF
    cG
    cQ
    cinv
    cfv
    #
    co
    #
    cfv
    #
    cfv
    #
    cJ
    cD
    cinv
    cfv
    #
    @7
    @9
    @24
    eqid
    #
    @29
    eqid
    #
    wph
    @18
    @1
    @23
    @21
    ad2antrr
    @14
    cB
    @24
    @4
    @6
    wph
    cB
    @24
    @6
    wf
    #
    @1
    wph
    cB
    @24
    cC
    cD
    @6
    cF
    c2nd
    cfv
    #
    fuciso.b
    @30
    wph
    @15
    wrel
    #
    @19
    @6
    @33
    @15
    wbr
    cC
    cD
    relfunc
    #
    fuciso.f
    cF
    @15
    1st2ndbr
    sylancr
    funcf1
    #
    adantr
    ffvelrnda
    @14
    cB
    @24
    @4
    @8
    wph
    cB
    @24
    @8
    wf
    #
    @1
    wph
    cB
    @24
    cC
    cD
    @8
    cG
    c2nd
    cfv
    #
    fuciso.b
    @30
    wph
    @34
    cG
    @15
    wcel
    #
    @8
    @38
    @15
    wbr
    @35
    fuciso.g
    cG
    @15
    1st2ndbr
    sylancr
    funcf1
    #
    adantr
    ffvelrnda
    fuciso.j
    @14
    @5
    @28
    @7
    @9
    @29
    co
    wbr
    #
    vx
    cB
    @14
    @3
    @27
    cG
    cF
    cN
    co
    wcel
    #
    @41
    vx
    cB
    wral
    #
    @14
    cA
    @27
    @26
    wbr
    #
    @3
    @42
    @43
    w3a
    #
    wph
    @1
    @44
    wph
    @1
    cA
    @26
    cdm
    #
    wcel
    #
    @44
    wph
    @0
    @46
    cA
    wph
    @15
    cQ
    cI
    @25
    cF
    cG
    @16
    @25
    eqid
    #
    @22
    fuciso.f
    fuciso.g
    fuciso.i
    isoval
    eleq2d
    wph
    @26
    wfun
    @47
    @44
    wb
    wph
    @15
    cQ
    @25
    cF
    cG
    @16
    @48
    @22
    fuciso.f
    fuciso.g
    invfun
    cA
    @26
    funfvbrb
    syl
    bitrd
    biimpa
    wph
    @44
    @45
    wb
    @1
    wph
    vx
    cB
    cC
    cD
    cQ
    cA
    cF
    cG
    @25
    @29
    cN
    @27
    fuciso.q
    fuciso.b
    fuciso.n
    fuciso.f
    fuciso.g
    @48
    @31
    fucinv
    adantr
    mpbid
    simp3d
    r19.21bi
    inviso1
    ralrimiva
    jca
    wph
    @13
    wa
    #
    @15
    cQ
    cA
    vy
    cB
    vy
    cv
    #
    cA
    cfv
    #
    @50
    @6
    cfv
    #
    @50
    @8
    cfv
    #
    @29
    co
    #
    cfv
    #
    cmpt
    cI
    @25
    cF
    cG
    @16
    @48
    wph
    cQ
    ccat
    wcel
    @13
    @22
    adantr
    wph
    @19
    @13
    fuciso.f
    adantr
    #
    wph
    @39
    @13
    fuciso.g
    adantr
    #
    fuciso.i
    @49
    vy
    cB
    cC
    cD
    cQ
    cA
    cF
    cG
    @25
    @29
    cN
    @55
    fuciso.q
    fuciso.b
    fuciso.n
    @56
    @57
    @48
    @31
    wph
    @3
    @12
    simprl
    @49
    @50
    cB
    wcel
    #
    wa
    #
    @51
    @54
    cdm
    #
    wcel
    #
    @51
    @55
    @54
    wbr
    #
    @59
    @51
    @52
    @53
    cJ
    co
    #
    @60
    @49
    @12
    @58
    @51
    @63
    wcel
    #
    wph
    @3
    @12
    simprr
    @11
    @64
    vx
    @50
    cB
    vx
    vy
    weq
    #
    @5
    @51
    @10
    @63
    @4
    @50
    cA
    fveq2
    @65
    @7
    @52
    @9
    @53
    cJ
    @4
    @50
    @6
    fveq2
    @4
    @50
    @8
    fveq2
    oveq12d
    eleq12d
    rspccva
    sylan
    @59
    @24
    cD
    cJ
    @29
    @52
    @53
    @30
    @31
    wph
    @18
    @13
    @58
    @21
    ad2antrr
    #
    @49
    cB
    @24
    @50
    @6
    wph
    @32
    @13
    @36
    adantr
    ffvelrnda
    #
    @49
    cB
    @24
    @50
    @8
    wph
    @37
    @13
    @40
    adantr
    ffvelrnda
    #
    fuciso.j
    isoval
    eleqtrd
    @59
    @54
    wfun
    @61
    @62
    wb
    @59
    @24
    cD
    @29
    @52
    @53
    @30
    @31
    @66
    @67
    @68
    invfun
    @51
    @54
    funfvbrb
    syl
    mpbid
    invfuc
    inviso1
    impbida
end
