include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wceq.mm"
include "simprr.mm"
include "wi.mm"
include "wb.mm"
include "zlem1lt.mm"
include "ancoms.mm"
include "biimprcd.mm"
include "adantr.mm"
include "impcom.mm"
include "cr.mm"
include "zre.mm"
include "letri3.mm"
include "syl2an.mm"
include "mpbir2and.mm"
include "ex.mm"

theorem zgtp1leeq
  let cA: class A
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( I e. ZZ /\ A e. ZZ ) -> ( ( ( A - 1 ) < I /\ I <_ A ) -> I = A ) )

  proof
    cI
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    #
    cA
    c1
    cmin
    co
    cI
    clt
    wbr
    #
    cI
    cA
    cle
    wbr
    #
    wa
    #
    cI
    cA
    wceq
    #
    @2
    @5
    wa
    @6
    @4
    cA
    cI
    cle
    wbr
    #
    @2
    @3
    @4
    simprr
    @5
    @2
    @7
    @3
    @2
    @7
    wi
    @4
    @2
    @7
    @3
    @1
    @0
    @7
    @3
    wb
    cA
    cI
    zlem1lt
    ancoms
    biimprcd
    adantr
    impcom
    @2
    @6
    @4
    @7
    wa
    wb
    #
    @5
    @0
    cI
    cr
    wcel
    cA
    cr
    wcel
    @8
    @1
    cI
    zre
    cA
    zre
    cI
    cA
    letri3
    syl2an
    adantr
    mpbir2and
    ex
end
