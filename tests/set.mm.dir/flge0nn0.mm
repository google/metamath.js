include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "cn0.mm"
include "flcl.mm"
include "adantr.mm"
include "wb.mm"
include "0z.mm"
include "flge.mm"
include "mpan2.mm"
include "biimpa.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem flge0nn0
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( |_ ` A ) e. NN0 )

  proof
    cA
    cr
    wcel
    #
    cc0
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
    cc0
    @2
    cle
    wbr
    #
    @2
    cn0
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
    cc0
    cz
    wcel
    @1
    @4
    wb
    0z
    cA
    cc0
    flge
    mpan2
    biimpa
    @2
    elnn0z
    sylanbrc
end
