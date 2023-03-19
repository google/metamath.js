include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "cr.mm"
include "wceq.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "infeq1d.mm"
include "xrltso.mm"
include "infex.mm"
include "fvmpt.mm"

theorem liminfgval
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let vx: setvar x
  assume liminfgval.1: |- G = ( k e. RR |-> inf ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint M k
  disjoint k x
  assert |- ( M e. RR -> ( G ` M ) = inf ( ( ( F " ( M [,) +oo ) ) i^i RR* ) , RR* , < ) )

  proof
    vk
    cM
    cF
    vk
    cv
    #
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
    cF
    cM
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
    cr
    cG
    @0
    cM
    wceq
    #
    cxr
    @3
    @6
    clt
    @7
    @2
    @5
    cxr
    @7
    @1
    @4
    cF
    @0
    cM
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    infeq1d
    liminfgval.1
    cxr
    @6
    clt
    xrltso
    infex
    fvmpt
end
