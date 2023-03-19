include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "pjop.mm"
include "mp2an.mm"

theorem pjopi
  let cA: class A
  let cH: class H
  assume pjop.1: |- H e. CH
  assume pjop.2: |- A e. ~H


  assert |- ( ( projh ` ( _|_ ` H ) ) ` A ) = ( A -h ( ( projh ` H ) ` A ) )

  proof
    cH
    cch
    wcel
    cA
    chil
    wcel
    cA
    cH
    cort
    cfv
    cpjh
    cfv
    cfv
    cA
    cA
    cH
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
    pjop
    mp2an
end
