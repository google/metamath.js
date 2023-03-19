include "c1st.mm"
include "cfv.mm"
include "cfunc.mm"
include "co.mm"
include "cfuc.mm"
include "c2nd.mm"
include "eqid.mm"
include "fucbas.mm"
include "wrel.mm"
include "wcel.mm"
include "wbr.mm"
include "relfunc.mm"
include "diagcl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"

theorem diag1cl
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cK: class K
  let cL: class L
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  assume diagval.l: |- L = ( C DiagFunc D )
  assume diagval.c: |- ( ph -> C e. Cat )
  assume diagval.d: |- ( ph -> D e. Cat )
  assume diag11.a: |- A = ( Base ` C )
  assume diag11.c: |- ( ph -> X e. A )
  assume diag11.k: |- K = ( ( 1st ` L ) ` X )


  assert |- ( ph -> K e. ( D Func C ) )

  proof
    wph
    cK
    cX
    cL
    c1st
    cfv
    #
    cfv
    cD
    cC
    cfunc
    co
    #
    diag11.k
    wph
    cA
    @1
    cX
    @0
    wph
    cA
    @1
    cC
    cD
    cC
    cfuc
    co
    #
    @0
    cL
    c2nd
    cfv
    #
    diag11.a
    cD
    cC
    @2
    @2
    eqid
    #
    fucbas
    wph
    cC
    @2
    cfunc
    co
    #
    wrel
    cL
    @5
    wcel
    @0
    @3
    @5
    wbr
    cC
    @2
    relfunc
    wph
    cC
    cD
    @2
    cL
    diagval.l
    diagval.c
    diagval.d
    @4
    diagcl
    cL
    @5
    1st2ndbr
    sylancr
    funcf1
    diag11.c
    ffvelrnd
    syl5eqel
end
