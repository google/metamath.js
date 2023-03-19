include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "cvv.mm"
include "clsi.mm"
include "df-liminf.mm"
include "wceq.mm"
include "imaeq1.mm"
include "ineq1d.mm"
include "infeq1d.mm"
include "mpteq2dv.mm"
include "a1i.mm"
include "eqtr4d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "adantl.mm"
include "elex.mm"
include "xrltso.mm"
include "supex.mm"
include "fvmptd2.mm"

theorem liminfval
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume liminfval.1: |- G = ( k e. RR |-> inf ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint G x
  disjoint V x
  disjoint k x
  assert |- ( F e. V -> ( liminf ` F ) = sup ( ran G , RR* , < ) )

  proof
    cF
    cV
    wcel
    #
    vx
    cF
    vk
    cr
    vx
    cv
    #
    vk
    cv
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cG
    crn
    #
    cxr
    clt
    csup
    #
    cvv
    clsi
    cvv
    vx
    vk
    df-liminf
    @1
    cF
    wceq
    #
    @8
    @10
    wceq
    @0
    @11
    cxr
    @7
    @9
    clt
    @11
    @6
    cG
    @11
    @6
    vk
    cr
    cF
    @2
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    cG
    @11
    vk
    cr
    @5
    @14
    @11
    cxr
    @4
    @13
    clt
    @11
    @3
    @12
    cxr
    @1
    cF
    @2
    imaeq1
    ineq1d
    infeq1d
    mpteq2dv
    cG
    @15
    wceq
    @11
    liminfval.1
    a1i
    eqtr4d
    rneqd
    supeq1d
    adantl
    cF
    cV
    elex
    @10
    cvv
    wcel
    @0
    cxr
    @9
    clt
    xrltso
    supex
    a1i
    fvmptd2
end
