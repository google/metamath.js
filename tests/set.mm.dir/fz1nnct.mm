include "cn.mm"
include "wceq.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "nnct.mm"
include "breq1.mm"
include "mpbiri.mm"
include "cfn.mm"
include "wcel.mm"
include "fzofi.mm"
include "fict.mm"
include "ax-mp.mm"
include "jaoi.mm"

theorem fz1nnct
  let cA: class A
  let cM: class M


  assert |- ( ( A = NN \/ A = ( 1 ..^ M ) ) -> A ~<_ _om )

  proof
    cA
    cn
    wceq
    #
    cA
    com
    cdom
    wbr
    #
    cA
    c1
    cM
    cfzo
    co
    #
    wceq
    #
    @0
    @1
    cn
    com
    cdom
    wbr
    nnct
    cA
    cn
    com
    cdom
    breq1
    mpbiri
    @3
    @1
    @2
    com
    cdom
    wbr
    #
    @2
    cfn
    wcel
    @4
    c1
    cM
    fzofi
    @2
    fict
    ax-mp
    cA
    @2
    com
    cdom
    breq1
    mpbiri
    jaoi
end
