include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wceq.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "xrltso.mm"
include "supex.mm"
include "fvmpt.mm"

theorem limsupgval
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint M k
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
  assert |- ( M e. RR -> ( G ` M ) = sup ( ( ( F " ( M [,) +oo ) ) i^i RR* ) , RR* , < ) )

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
    csup
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
    csup
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
    supeq1d
    limsupval.1
    cxr
    @6
    clt
    xrltso
    supex
    fvmpt
end
