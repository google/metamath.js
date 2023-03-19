include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "cnghm.mm"
include "cfv.mm"
include "cr.mm"
include "nmhmnghm.mm"
include "nghmcl.mm"
include "syl.mm"

theorem nmhmcl
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  assume isnmhm2.1: |- N = ( S normOp T )


  assert |- ( F e. ( S NMHom T ) -> ( N ` F ) e. RR )

  proof
    cF
    cS
    cT
    cnmhm
    co
    wcel
    cF
    cS
    cT
    cnghm
    co
    wcel
    cF
    cN
    cfv
    cr
    wcel
    cS
    cT
    cF
    nmhmnghm
    cS
    cT
    cF
    cN
    isnmhm2.1
    nghmcl
    syl
end
