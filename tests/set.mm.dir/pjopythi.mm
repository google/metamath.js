include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cpjh.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cva.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "pjoi0i.mm"
include "pjhclii.mm"
include "normpythi.mm"
include "syl.mm"

theorem pjopythi
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjoi0.1: |- G e. CH
  assume pjoi0.2: |- H e. CH
  assume pjoi0.3: |- A e. ~H


  assert |- ( G C_ ( _|_ ` H ) -> ( ( normh ` ( ( ( projh ` G ) ` A ) +h ( ( projh ` H ) ` A ) ) ) ^ 2 ) = ( ( ( normh ` ( ( projh ` G ) ` A ) ) ^ 2 ) + ( ( normh ` ( ( projh ` H ) ` A ) ) ^ 2 ) ) )

  proof
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
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    csp
    co
    cc0
    wceq
    @0
    @1
    cva
    co
    cno
    cfv
    c2
    cexp
    co
    @0
    cno
    cfv
    c2
    cexp
    co
    @1
    cno
    cfv
    c2
    cexp
    co
    caddc
    co
    wceq
    cA
    cG
    cH
    pjoi0.1
    pjoi0.2
    pjoi0.3
    pjoi0i
    @0
    @1
    cA
    cG
    pjoi0.1
    pjoi0.3
    pjhclii
    cA
    cH
    pjoi0.2
    pjoi0.3
    pjhclii
    normpythi
    syl
end
