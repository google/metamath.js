include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wceq.mm"
include "simprr.mm"
include "wb.mm"
include "zleltp1.mm"
include "adantr.mm"
include "mpbird.mm"
include "simprl.mm"
include "cr.mm"
include "zre.mm"
include "letri3.mm"
include "syl2an.mm"
include "mpbir2and.mm"
include "ex.mm"

theorem zgeltp1eq
  let cA: class A
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( I e. ZZ /\ A e. ZZ ) -> ( ( A <_ I /\ I < ( A + 1 ) ) -> I = A ) )

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
    cI
    cle
    wbr
    #
    cI
    cA
    c1
    caddc
    co
    clt
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
    #
    @6
    cI
    cA
    cle
    wbr
    #
    @3
    @7
    @8
    @4
    @2
    @3
    @4
    simprr
    @2
    @8
    @4
    wb
    @5
    cI
    cA
    zleltp1
    adantr
    mpbird
    @2
    @3
    @4
    simprl
    @2
    @6
    @8
    @3
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
    @9
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
