include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "mnflt.mm"
include "mnfltpnf.mm"
include "breq2.mm"
include "mpbiri.mm"
include "jaoi.mm"

theorem mnfltxr
  let cA: class A


  assert |- ( ( A e. RR \/ A = +oo ) -> -oo < A )

  proof
    cA
    cr
    wcel
    cmnf
    cA
    clt
    wbr
    #
    cA
    cpnf
    wceq
    #
    cA
    mnflt
    @1
    @0
    cmnf
    cpnf
    clt
    wbr
    mnfltpnf
    cA
    cpnf
    cmnf
    clt
    breq2
    mpbiri
    jaoi
end
