include "ccau.mm"
include "wcel.mm"
include "cn.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "hcau.mm"
include "baib.mm"

theorem seq1hcau
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let vf: setvar f
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( F : NN --> ~H -> ( F e. Cauchy <-> A. x e. RR+ E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( F ` y ) -h ( F ` z ) ) ) < x ) )

  proof
    cF
    ccau
    wcel
    cn
    chil
    cF
    wf
    vy
    cv
    #
    cF
    cfv
    vz
    cv
    cF
    cfv
    cmv
    co
    cno
    cfv
    vx
    cv
    clt
    wbr
    vz
    @0
    cuz
    cfv
    wral
    vy
    cn
    wrex
    vx
    crp
    wral
    vx
    vy
    vz
    cF
    hcau
    baib
end
