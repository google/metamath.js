include "cfn.mm"
include "wcel.mm"
include "cevpm.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "psgnevpmb.mm"
include "simplbda.mm"

theorem psgnevpm
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cN: class N
  let vd: setvar d
  assume evpmss.s: |- S = ( SymGrp ` D )
  assume evpmss.p: |- P = ( Base ` S )
  assume psgnevpmb.n: |- N = ( pmSgn ` D )


  assert |- ( ( D e. Fin /\ F e. ( pmEven ` D ) ) -> ( N ` F ) = 1 )

  proof
    cD
    cfn
    wcel
    cF
    cD
    cevpm
    cfv
    wcel
    cF
    cP
    wcel
    cF
    cN
    cfv
    c1
    wceq
    cD
    cP
    cS
    cF
    cN
    evpmss.s
    evpmss.p
    psgnevpmb.n
    psgnevpmb
    simplbda
end
