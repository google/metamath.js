include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "cn.mm"
include "flcl.mm"
include "adantr.mm"
include "wb.mm"
include "1z.mm"
include "flge.mm"
include "mpan2.mm"
include "biimpa.mm"
include "elnnz1.mm"
include "sylanbrc.mm"

theorem flge1nn
  let cA: class A


  assert |- ( ( A e. RR /\ 1 <_ A ) -> ( |_ ` A ) e. NN )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    cA
    cfl
    cfv
    #
    cz
    wcel
    #
    c1
    @2
    cle
    wbr
    #
    @2
    cn
    wcel
    @0
    @3
    @1
    cA
    flcl
    adantr
    @0
    @1
    @4
    @0
    c1
    cz
    wcel
    @1
    @4
    wb
    1z
    cA
    c1
    flge
    mpan2
    biimpa
    @2
    elnnz1
    sylanbrc
end
