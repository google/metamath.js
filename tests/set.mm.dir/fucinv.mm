include "csect.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "c1st.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "fucsect.mm"
include "anbi12d.mm"
include "cfunc.mm"
include "fucbas.mm"
include "ccat.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "fuccat.mm"
include "isinv.mm"
include "cbs.mm"
include "adantr.mm"
include "c2nd.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnda.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "df-3an.mm"
include "3ancoma.mm"
include "bitri.mm"
include "anbi12i.mm"
include "anandi.mm"
include "bitr4i.mm"
include "3bitr4g.mm"
include "3bitr4d.mm"

theorem fucinv
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cN: class N
  let cV: class V
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vz: setvar z
  let cX: class X
  assume fuciso.q: |- Q = ( C FuncCat D )
  assume fuciso.b: |- B = ( Base ` C )
  assume fuciso.n: |- N = ( C Nat D )
  assume fuciso.f: |- ( ph -> F e. ( C Func D ) )
  assume fuciso.g: |- ( ph -> G e. ( C Func D ) )
  assume fucinv.i: |- I = ( Inv ` Q )
  assume fucinv.j: |- J = ( Inv ` D )

  disjoint B x
  disjoint C x
  disjoint D x
  disjoint I x
  disjoint F x
  disjoint G x
  disjoint J x
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
  assert |- ( ph -> ( U ( F I G ) V <-> ( U e. ( F N G ) /\ V e. ( G N F ) /\ A. x e. B ( U ` x ) ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) ( V ` x ) ) ) )

  proof
    wph
    cU
    cV
    cF
    cG
    cQ
    csect
    cfv
    #
    co
    wbr
    #
    cV
    cU
    cG
    cF
    @0
    co
    wbr
    #
    wa
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
    vx
    cv
    #
    cU
    cfv
    #
    @5
    cV
    cfv
    #
    @5
    cF
    c1st
    cfv
    #
    cfv
    #
    @5
    cG
    c1st
    cfv
    #
    cfv
    #
    cD
    csect
    cfv
    #
    co
    wbr
    #
    vx
    cB
    wral
    #
    w3a
    #
    @4
    @3
    @7
    @6
    @11
    @9
    @12
    co
    wbr
    #
    vx
    cB
    wral
    #
    w3a
    #
    wa
    #
    cU
    cV
    cF
    cG
    cI
    co
    wbr
    @3
    @4
    @6
    @7
    @9
    @11
    cJ
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
    @1
    @15
    @2
    @18
    wph
    vx
    cB
    cC
    cD
    cQ
    @0
    @12
    cU
    cF
    cG
    cN
    cV
    fuciso.q
    fuciso.b
    fuciso.n
    fuciso.f
    fuciso.g
    @0
    eqid
    #
    @12
    eqid
    #
    fucsect
    wph
    vx
    cB
    cC
    cD
    cQ
    @0
    @12
    cV
    cG
    cF
    cN
    cU
    fuciso.q
    fuciso.b
    fuciso.n
    fuciso.g
    fuciso.f
    @23
    @24
    fucsect
    anbi12d
    wph
    cC
    cD
    cfunc
    co
    #
    cQ
    @0
    cU
    cV
    cI
    cF
    cG
    cC
    cD
    cQ
    fuciso.q
    fucbas
    fucinv.i
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
    @25
    wcel
    #
    @26
    @27
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
    @26
    @27
    @29
    simprd
    #
    fuccat
    fuciso.f
    fuciso.g
    @23
    isinv
    wph
    @3
    @4
    wa
    #
    @21
    wa
    @31
    @14
    @17
    wa
    #
    wa
    #
    @22
    @19
    wph
    @21
    @32
    @31
    wph
    @21
    @13
    @16
    wa
    #
    vx
    cB
    wral
    @32
    wph
    @20
    @34
    vx
    cB
    wph
    @5
    cB
    wcel
    #
    wa
    cD
    cbs
    cfv
    #
    cD
    @12
    @6
    @7
    cJ
    @9
    @11
    @36
    eqid
    #
    fucinv.j
    wph
    @27
    @35
    @30
    adantr
    wph
    cB
    @36
    @5
    @8
    wph
    cB
    @36
    cC
    cD
    @8
    cF
    c2nd
    cfv
    #
    fuciso.b
    @37
    wph
    @25
    wrel
    #
    @28
    @8
    @38
    @25
    wbr
    cC
    cD
    relfunc
    #
    fuciso.f
    cF
    @25
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    wph
    cB
    @36
    @5
    @10
    wph
    cB
    @36
    cC
    cD
    @10
    cG
    c2nd
    cfv
    #
    fuciso.b
    @37
    wph
    @39
    cG
    @25
    wcel
    @10
    @41
    @25
    wbr
    @40
    fuciso.g
    cG
    @25
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @24
    isinv
    ralbidva
    @13
    @16
    vx
    cB
    r19.26
    syl6bb
    anbi2d
    @3
    @4
    @21
    df-3an
    @19
    @31
    @14
    wa
    #
    @31
    @17
    wa
    #
    wa
    @33
    @15
    @42
    @18
    @43
    @3
    @4
    @14
    df-3an
    @18
    @3
    @4
    @17
    w3a
    @43
    @4
    @3
    @17
    3ancoma
    @3
    @4
    @17
    df-3an
    bitri
    anbi12i
    @31
    @14
    @17
    anandi
    bitr4i
    3bitr4g
    3bitr4d
end
