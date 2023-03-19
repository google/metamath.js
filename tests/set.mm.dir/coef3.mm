include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "cn0.mm"
include "wf.mm"
include "plyssc.mm"
include "sseli.mm"
include "0cn.mm"
include "coef2.mm"
include "sylancl.mm"

theorem coef3
  let cA: class A
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let vz: setvar z
  assume dgrval.1: |- A = ( coeff ` F )


  assert |- ( F e. ( Poly ` S ) -> A : NN0 --> CC )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cF
    cc
    cply
    cfv
    #
    wcel
    cc0
    cc
    wcel
    cn0
    cc
    cA
    wf
    @0
    @1
    cF
    cS
    plyssc
    sseli
    0cn
    cA
    cc
    cF
    dgrval.1
    coef2
    sylancl
end
