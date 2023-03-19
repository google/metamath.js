include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "zmulcl.mm"
include "anidms.mm"
include "adantr.mm"
include "cr.mm"
include "zre.mm"
include "msqgt0.mm"
include "sylan.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem msqznn
  let cA: class A


  assert |- ( ( A e. ZZ /\ A =/= 0 ) -> ( A x. A ) e. NN )

  proof
    cA
    cz
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cA
    cA
    cmul
    co
    #
    cz
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @2
    cn
    wcel
    @0
    @3
    @1
    @0
    @3
    cA
    cA
    zmulcl
    anidms
    adantr
    @0
    cA
    cr
    wcel
    @1
    @4
    cA
    zre
    cA
    msqgt0
    sylan
    @2
    elnnz
    sylanbrc
end
