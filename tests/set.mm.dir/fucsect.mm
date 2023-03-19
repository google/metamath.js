include "co.mm"
include "wbr.mm"
include "wcel.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "ccid.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "c1st.mm"
include "wral.mm"
include "cfunc.mm"
include "fucbas.mm"
include "fuchom.mm"
include "eqid.mm"
include "ccat.mm"
include "wa.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "fuccat.mm"
include "issect.mm"
include "cmpt.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "mp1i.mm"
include "simprl.mm"
include "simprr.mm"
include "fucco.mm"
include "ccom.mm"
include "adantr.mm"
include "fucid.mm"
include "cbs.mm"
include "wf.mm"
include "wfn.mm"
include "cidfn.mm"
include "dffn2.mm"
include "sylib.mm"
include "c2nd.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "chom.mm"
include "ffvelrnda.mm"
include "nat1st2nd.mm"
include "simpr.mm"
include "natcl.mm"
include "issect2.mm"
include "ralbidva.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem fucsect
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vz: setvar z
  let cI: class I
  let cJ: class J
  let cX: class X
  assume fuciso.q: |- Q = ( C FuncCat D )
  assume fuciso.b: |- B = ( Base ` C )
  assume fuciso.n: |- N = ( C Nat D )
  assume fuciso.f: |- ( ph -> F e. ( C Func D ) )
  assume fuciso.g: |- ( ph -> G e. ( C Func D ) )
  assume fucsect.s: |- S = ( Sect ` Q )
  assume fucsect.t: |- T = ( Sect ` D )

  disjoint B x
  disjoint C x
  disjoint D x
  disjoint F x
  disjoint G x
  disjoint N x
  disjoint V x
  disjoint ph x
  disjoint Q x
  disjoint U x
  disjoint x y
  disjoint A x
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
  disjoint I x
  disjoint I y
  disjoint F f
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint J x
  disjoint J y
  disjoint N y
  disjoint V f
  disjoint V y
  disjoint V z
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint Q y
  disjoint U y
  disjoint X f
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( U ( F S G ) V <-> ( U e. ( F N G ) /\ V e. ( G N F ) /\ A. x e. B ( U ` x ) ( ( ( 1st ` F ) ` x ) T ( ( 1st ` G ) ` x ) ) ( V ` x ) ) ) )

  proof
    wph
    cU
    cV
    cF
    cG
    cS
    co
    wbr
    cU
    cF
    cG
    cN
    co
    wcel
    #
    cV
    cG
    cF
    cN
    co
    wcel
    #
    cV
    cU
    cF
    cG
    cop
    cF
    cQ
    cco
    cfv
    #
    co
    co
    #
    cF
    cQ
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    w3a
    #
    @0
    @1
    vx
    cv
    #
    cU
    cfv
    #
    @8
    cV
    cfv
    #
    @8
    cF
    c1st
    cfv
    #
    cfv
    #
    @8
    cG
    c1st
    cfv
    #
    cfv
    #
    cT
    co
    wbr
    #
    vx
    cB
    wral
    #
    w3a
    #
    wph
    cC
    cD
    cfunc
    co
    #
    cQ
    cS
    @2
    @4
    cU
    cV
    cN
    cF
    cG
    cC
    cD
    cQ
    fuciso.q
    fucbas
    cC
    cD
    cQ
    cN
    fuciso.q
    fuciso.n
    fuchom
    @2
    eqid
    #
    @4
    eqid
    #
    fucsect.s
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
    @18
    wcel
    #
    @21
    @22
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
    @21
    @22
    @24
    simprd
    #
    fuccat
    fuciso.f
    fuciso.g
    issect
    wph
    @0
    @1
    wa
    #
    @6
    wa
    @26
    @16
    wa
    @7
    @17
    wph
    @26
    @6
    @16
    wph
    @26
    wa
    #
    vx
    cB
    @10
    @9
    @12
    @14
    cop
    @12
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    vx
    cB
    @12
    cD
    ccid
    cfv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    @30
    @33
    wceq
    #
    vx
    cB
    wral
    #
    @6
    @16
    @30
    cvv
    wcel
    #
    vx
    cB
    wral
    @35
    @37
    wb
    @27
    @38
    vx
    cB
    @10
    @9
    @29
    ovex
    rgenw
    vx
    cB
    @30
    @33
    cvv
    mpteqb
    mp1i
    @27
    @3
    @31
    @5
    @34
    @27
    vx
    cB
    cC
    cD
    cQ
    cU
    cV
    @2
    @28
    cF
    cG
    cF
    cN
    fuciso.q
    fuciso.n
    fuciso.b
    @28
    eqid
    #
    @19
    wph
    @0
    @1
    simprl
    #
    wph
    @0
    @1
    simprr
    #
    fucco
    @27
    @5
    @32
    @11
    ccom
    #
    @34
    @27
    cC
    cD
    cQ
    @32
    cF
    @4
    fuciso.q
    @20
    @32
    eqid
    #
    wph
    @23
    @26
    fuciso.f
    adantr
    fucid
    @27
    cD
    cbs
    cfv
    #
    cvv
    @32
    wf
    #
    cB
    @44
    @11
    wf
    #
    @42
    @34
    wceq
    @27
    @32
    @44
    wfn
    #
    @45
    @27
    @22
    @47
    wph
    @22
    @26
    @25
    adantr
    #
    @44
    cD
    @32
    @44
    eqid
    #
    @43
    cidfn
    syl
    @44
    @32
    dffn2
    sylib
    wph
    @46
    @26
    wph
    cB
    @44
    cC
    cD
    @11
    cF
    c2nd
    cfv
    #
    fuciso.b
    @49
    wph
    @18
    wrel
    #
    @23
    @11
    @50
    @18
    wbr
    cC
    cD
    relfunc
    #
    fuciso.f
    cF
    @18
    1st2ndbr
    sylancr
    funcf1
    adantr
    #
    vx
    @32
    @11
    cB
    @44
    cvv
    fcompt
    syl2anc
    eqtrd
    eqeq12d
    @27
    @15
    @36
    vx
    cB
    @27
    @8
    cB
    wcel
    #
    wa
    #
    @44
    cD
    cT
    @28
    @32
    @9
    @10
    cD
    chom
    cfv
    #
    @12
    @14
    @49
    @56
    eqid
    #
    @39
    @43
    fucsect.t
    @27
    @22
    @54
    @48
    adantr
    @27
    cB
    @44
    @8
    @11
    @53
    ffvelrnda
    @27
    cB
    @44
    @8
    @13
    wph
    cB
    @44
    @13
    wf
    @26
    wph
    cB
    @44
    cC
    cD
    @13
    cG
    c2nd
    cfv
    #
    fuciso.b
    @49
    wph
    @51
    cG
    @18
    wcel
    @13
    @58
    @18
    wbr
    @52
    fuciso.g
    cG
    @18
    1st2ndbr
    sylancr
    funcf1
    adantr
    ffvelrnda
    @55
    cU
    cB
    cC
    cD
    @11
    @50
    @56
    @13
    @58
    cN
    @8
    fuciso.n
    @55
    cU
    cC
    cD
    cF
    cG
    cN
    fuciso.n
    @27
    @0
    @54
    @40
    adantr
    nat1st2nd
    fuciso.b
    @57
    @27
    @54
    simpr
    #
    natcl
    @55
    cV
    cB
    cC
    cD
    @13
    @58
    @56
    @11
    @50
    cN
    @8
    fuciso.n
    @55
    cV
    cC
    cD
    cG
    cF
    cN
    fuciso.n
    @27
    @1
    @54
    @41
    adantr
    nat1st2nd
    fuciso.b
    @57
    @59
    natcl
    issect2
    ralbidva
    3bitr4d
    pm5.32da
    @0
    @1
    @6
    df-3an
    @0
    @1
    @16
    df-3an
    3bitr4g
    bitrd
end
