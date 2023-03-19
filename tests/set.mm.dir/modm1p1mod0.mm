include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "caddc.mm"
include "cc0.mm"
include "1re.mm"
include "modaddmod.mm"
include "mp3an2.mm"
include "eqcomd.mm"
include "adantr.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cc.mm"
include "rpcn.mm"
include "npcan1.mm"
include "syl.mm"
include "modid0.mm"
include "eqtrd.mm"
include "adantl.mm"
include "sylan9eqr.mm"
include "ex.mm"

theorem modm1p1mod0
  let cA: class A
  let cM: class M


  assert |- ( ( A e. RR /\ M e. RR+ ) -> ( ( A mod M ) = ( M - 1 ) -> ( ( A + 1 ) mod M ) = 0 ) )

  proof
    cA
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    wa
    #
    cA
    cM
    cmo
    co
    #
    cM
    c1
    cmin
    co
    #
    wceq
    #
    cA
    c1
    caddc
    co
    cM
    cmo
    co
    #
    cc0
    wceq
    @2
    @5
    wa
    @6
    @3
    c1
    caddc
    co
    #
    cM
    cmo
    co
    #
    cc0
    @2
    @6
    @8
    wceq
    @5
    @2
    @8
    @6
    @0
    c1
    cr
    wcel
    @1
    @8
    @6
    wceq
    1re
    cA
    c1
    cM
    modaddmod
    mp3an2
    eqcomd
    adantr
    @5
    @2
    @8
    @4
    c1
    caddc
    co
    #
    cM
    cmo
    co
    #
    cc0
    @5
    @7
    @9
    cM
    cmo
    @3
    @4
    c1
    caddc
    oveq1
    oveq1d
    @1
    @10
    cc0
    wceq
    @0
    @1
    @10
    cM
    cM
    cmo
    co
    cc0
    @1
    @9
    cM
    cM
    cmo
    @1
    cM
    cc
    wcel
    @9
    cM
    wceq
    cM
    rpcn
    cM
    npcan1
    syl
    oveq1d
    cM
    modid0
    eqtrd
    adantl
    sylan9eqr
    eqtrd
    ex
end
