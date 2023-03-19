include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "ltadd2.mm"
include "notbid.mm"
include "simp2.mm"
include "simp1.mm"
include "simp3.mm"
include "ltadd2d.mm"
include "anbi12d.mm"
include "lttri3d.mm"
include "readdcld.mm"
include "3bitr4rd.mm"

theorem readdcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( C + A ) = ( C + B ) <-> A = B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    wn
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    wa
    cC
    cA
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    clt
    wbr
    #
    wn
    #
    @9
    @8
    clt
    wbr
    #
    wn
    #
    wa
    cA
    cB
    wceq
    @8
    @9
    wceq
    @3
    @5
    @11
    @7
    @13
    @3
    @4
    @10
    cA
    cB
    cC
    ltadd2
    notbid
    @3
    @6
    @12
    @3
    cB
    cA
    cC
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    ltadd2d
    notbid
    anbi12d
    @3
    cA
    cB
    @15
    @14
    lttri3d
    @3
    @8
    @9
    @3
    cC
    cA
    @16
    @15
    readdcld
    @3
    cC
    cB
    @16
    @14
    readdcld
    lttri3d
    3bitr4rd
end
