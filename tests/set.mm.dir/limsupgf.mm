include "cr.mm"
include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "wcel.mm"
include "inss2.mm"
include "supxrcl.mm"
include "mp1i.mm"
include "fmpti.mm"

theorem limsupgf
  let vk: setvar k
  let cF: class F
  let cG: class G
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
  assert |- G : RR --> RR*

  proof
    vk
    cr
    cxr
    cF
    vk
    cv
    #
    cpnf
    cico
    co
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cG
    limsupval.1
    @2
    cxr
    wss
    @3
    cxr
    wcel
    @0
    cr
    wcel
    @1
    cxr
    inss2
    @2
    supxrcl
    mp1i
    fmpti
end
