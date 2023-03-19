include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cc0.mm"
include "rpgt0.mm"
include "3ad2ant3.mm"
include "rpre.mm"
include "simp1.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "wa.mm"
include "wi.mm"
include "simpl.mm"
include "adantl.mm"
include "readdcld.mm"
include "3adant2.mm"
include "simp2.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"

theorem addlelt
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( M e. RR /\ N e. RR /\ A e. RR+ ) -> ( ( M + A ) <_ N -> M < N ) )

  proof
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cA
    crp
    wcel
    #
    w3a
    #
    cM
    cM
    cA
    caddc
    co
    #
    clt
    wbr
    #
    @4
    cN
    cle
    wbr
    #
    cM
    cN
    clt
    wbr
    #
    @3
    cc0
    cA
    clt
    wbr
    #
    @5
    @2
    @0
    @8
    @1
    cA
    rpgt0
    3ad2ant3
    @3
    cA
    cM
    @2
    @0
    cA
    cr
    wcel
    #
    @1
    cA
    rpre
    #
    3ad2ant3
    @0
    @1
    @2
    simp1
    #
    ltaddposd
    mpbid
    @3
    @0
    @4
    cr
    wcel
    #
    @1
    @5
    @6
    wa
    @7
    wi
    @11
    @0
    @2
    @12
    @1
    @0
    @2
    wa
    cM
    cA
    @0
    @2
    simpl
    @2
    @9
    @0
    @10
    adantl
    readdcld
    3adant2
    @0
    @1
    @2
    simp2
    cM
    @4
    cN
    ltletr
    syl3anc
    mpand
end
