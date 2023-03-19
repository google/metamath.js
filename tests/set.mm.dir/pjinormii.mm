include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csp.mm"
include "pjhclii.mm"
include "normsqi.mm"
include "pjadjii.mm"
include "pjidmi.mm"
include "oveq1i.mm"
include "3eqtr2ri.mm"

theorem pjinormii
  let cA: class A
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H


  assert |- ( ( ( projh ` H ) ` A ) .ih A ) = ( ( normh ` ( ( projh ` H ) ` A ) ) ^ 2 )

  proof
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    c2
    cexp
    co
    @1
    @1
    csp
    co
    @1
    @0
    cfv
    #
    cA
    csp
    co
    @1
    cA
    csp
    co
    @1
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    normsqi
    @1
    cA
    cH
    pjidm.1
    @3
    pjidm.2
    pjadjii
    @2
    @1
    cA
    csp
    cA
    cH
    pjidm.1
    pjidm.2
    pjidmi
    oveq1i
    3eqtr2ri
end
