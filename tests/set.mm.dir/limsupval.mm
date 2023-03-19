include "wcel.mm"
include "cvv.mm"
include "clsp.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "elex.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "csup.mm"
include "cmpt.mm"
include "imaeq1.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "df-limsup.mm"
include "xrltso.mm"
include "infex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem limsupval
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint k x
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint f k
  disjoint G x
  assert |- ( F e. V -> ( limsup ` F ) = inf ( ran G , RR* , < ) )

  proof
    cF
    cV
    wcel
    cF
    cvv
    wcel
    cF
    clsp
    cfv
    cG
    crn
    #
    cxr
    clt
    cinf
    #
    wceq
    cF
    cV
    elex
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
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    @1
    cvv
    clsp
    @2
    cF
    wceq
    #
    cxr
    @8
    @0
    clt
    @9
    @7
    cG
    @9
    @7
    vk
    cr
    cF
    @3
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    cG
    @9
    vk
    cr
    @6
    @12
    @9
    cxr
    @5
    @11
    clt
    @9
    @4
    @10
    cxr
    @2
    cF
    @3
    imaeq1
    ineq1d
    supeq1d
    mpteq2dv
    limsupval.1
    syl6eqr
    rneqd
    infeq1d
    vx
    vk
    df-limsup
    cxr
    @0
    clt
    xrltso
    infex
    fvmpt
    syl
end
