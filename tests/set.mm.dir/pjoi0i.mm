include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cpjh.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "3pm3.2i.mm"
include "pjoi0.mm"
include "mpan.mm"

theorem pjoi0i
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjoi0.1: |- G e. CH
  assume pjoi0.2: |- H e. CH
  assume pjoi0.3: |- A e. ~H


  assert |- ( G C_ ( _|_ ` H ) -> ( ( ( projh ` G ) ` A ) .ih ( ( projh ` H ) ` A ) ) = 0 )

  proof
    cG
    cch
    wcel
    #
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    w3a
    cG
    cH
    cort
    cfv
    wss
    cA
    cG
    cpjh
    cfv
    cfv
    cA
    cH
    cpjh
    cfv
    cfv
    csp
    co
    cc0
    wceq
    @0
    @1
    @2
    pjoi0.1
    pjoi0.2
    pjoi0.3
    3pm3.2i
    cA
    cG
    cH
    pjoi0
    mpan
end
