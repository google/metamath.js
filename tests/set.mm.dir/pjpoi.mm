include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "pjpo.mm"
include "mp2an.mm"

theorem pjpoi
  let cA: class A
  let cH: class H
  assume pjop.1: |- H e. CH
  assume pjop.2: |- A e. ~H


  assert |- ( ( projh ` H ) ` A ) = ( A -h ( ( projh ` ( _|_ ` H ) ) ` A ) )

  proof
    cH
    cch
    wcel
    cA
    chil
    wcel
    cA
    cH
    cpjh
    cfv
    cfv
    cA
    cA
    cH
    cort
    cfv
    cpjh
    cfv
    cfv
    cmv
    co
    wceq
    pjop.1
    pjop.2
    cA
    cH
    pjpo
    mp2an
end
