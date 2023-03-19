include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "ccnv.mm"
include "cc.mm"
include "cdif.mm"
include "cima.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "dgrlem.mm"
include "simpld.mm"

theorem coef
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


  assert |- ( F e. ( Poly ` S ) -> A : NN0 --> ( S u. { 0 } ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    cn0
    cS
    cc0
    csn
    #
    cun
    cA
    wf
    vx
    cv
    vn
    cv
    cle
    wbr
    vx
    cA
    ccnv
    cc
    @0
    cdif
    cima
    wral
    vn
    cz
    wrex
    vx
    cA
    cS
    vn
    cF
    dgrval.1
    dgrlem
    simpld
end
