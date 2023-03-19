include "cop.mm"
include "ccofu.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cfunc.mm"
include "wbr.mm"
include "wcel.mm"
include "df-br.mm"
include "sylib.mm"
include "cofuval.mm"
include "cvv.mm"
include "wa.mm"
include "wceq.mm"
include "wrel.mm"
include "relfunc.mm"
include "brrelex12.mm"
include "sylancr.mm"
include "op1stg.mm"
include "syl.mm"
include "coeq12d.mm"
include "w3a.mm"
include "op2ndg.mm"
include "3ad2ant1.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "oveqd.mm"
include "mpt2eq3dva.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem cofuval2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  assume cofuval2.b: |- B = ( Base ` C )
  assume cofuval2.f: |- ( ph -> F ( C Func D ) G )
  assume cofuval2.x: |- ( ph -> H ( D Func E ) K )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint ph y
  disjoint K x
  disjoint K y
  assert |- ( ph -> ( <. H , K >. o.func <. F , G >. ) = <. ( H o. F ) , ( x e. B , y e. B |-> ( ( ( F ` x ) K ( F ` y ) ) o. ( x G y ) ) ) >. )

  proof
    wph
    cH
    cK
    cop
    #
    cF
    cG
    cop
    #
    ccofu
    co
    @0
    c1st
    cfv
    #
    @1
    c1st
    cfv
    #
    ccom
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    @3
    cfv
    #
    vy
    cv
    #
    @3
    cfv
    #
    @0
    c2nd
    cfv
    #
    co
    #
    @5
    @7
    @1
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    cH
    cF
    ccom
    #
    vx
    vy
    cB
    cB
    @5
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cK
    co
    #
    @5
    @7
    cG
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    wph
    vx
    vy
    cB
    cC
    cD
    cE
    @1
    @0
    cofuval2.b
    wph
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    @1
    @22
    wcel
    cofuval2.f
    cF
    cG
    @22
    df-br
    sylib
    wph
    cH
    cK
    cD
    cE
    cfunc
    co
    #
    wbr
    #
    @0
    @24
    wcel
    cofuval2.x
    cH
    cK
    @24
    df-br
    sylib
    cofuval
    wph
    @4
    @15
    @14
    @21
    wph
    @2
    cH
    @3
    cF
    wph
    cH
    cvv
    wcel
    cK
    cvv
    wcel
    wa
    #
    @2
    cH
    wceq
    wph
    @24
    wrel
    @25
    @26
    cD
    cE
    relfunc
    cofuval2.x
    cH
    cK
    @24
    brrelex12
    sylancr
    #
    cH
    cK
    cvv
    cvv
    op1stg
    syl
    wph
    cF
    cvv
    wcel
    cG
    cvv
    wcel
    wa
    #
    @3
    cF
    wceq
    #
    wph
    @22
    wrel
    @23
    @28
    cC
    cD
    relfunc
    cofuval2.f
    cF
    cG
    @22
    brrelex12
    sylancr
    #
    cF
    cG
    cvv
    cvv
    op1stg
    syl
    #
    coeq12d
    wph
    vx
    vy
    cB
    cB
    @13
    @20
    wph
    @5
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    w3a
    #
    @10
    @18
    @12
    @19
    @34
    @6
    @16
    @8
    @17
    @9
    cK
    wph
    @32
    @9
    cK
    wceq
    #
    @33
    wph
    @26
    @35
    @27
    cH
    cK
    cvv
    cvv
    op2ndg
    syl
    3ad2ant1
    @34
    @5
    @3
    cF
    wph
    @32
    @29
    @33
    @31
    3ad2ant1
    #
    fveq1d
    @34
    @7
    @3
    cF
    @36
    fveq1d
    oveq123d
    @34
    @11
    cG
    @5
    @7
    wph
    @32
    @11
    cG
    wceq
    #
    @33
    wph
    @28
    @37
    @30
    cF
    cG
    cvv
    cvv
    op2ndg
    syl
    3ad2ant1
    oveqd
    coeq12d
    mpt2eq3dva
    opeq12d
    eqtrd
end
