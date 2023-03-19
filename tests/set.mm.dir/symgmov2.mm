include "wcel.mm"
include "wf1o.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "csymg.mm"
include "eqid.mm"
include "symgbasf1o.mm"
include "f1ofo.mm"
include "foelrni.mm"
include "ralrimiva.mm"
include "3syl.mm"

theorem symgmov2
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  assume symgmov1.p: |- P = ( Base ` ( SymGrp ` N ) )

  disjoint N k
  disjoint N n
  disjoint k n
  disjoint P n
  disjoint Q k
  disjoint Q n
  assert |- ( Q e. P -> A. n e. N E. k e. N ( Q ` k ) = n )

  proof
    cQ
    cP
    wcel
    cN
    cN
    cQ
    wf1o
    cN
    cN
    cQ
    wfo
    #
    vk
    cv
    cQ
    cfv
    vn
    cv
    #
    wceq
    vk
    cN
    wrex
    #
    vn
    cN
    wral
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    @3
    eqid
    symgmov1.p
    symgbasf1o
    cN
    cN
    cQ
    f1ofo
    @0
    @2
    vn
    cN
    vk
    cN
    cN
    cQ
    @1
    foelrni
    ralrimiva
    3syl
end
