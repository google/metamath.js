include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cpnf.mm"
include "0lepnf.mm"
include "oveq2.mm"
include "pc0.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "syl5breqr.mm"
include "wne.mm"
include "pczcl.mm"
include "nn0ge0d.mm"
include "anassrs.mm"
include "pm2.61dane.mm"

theorem pcge0
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ N e. ZZ ) -> 0 <_ ( P pCnt N ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cc0
    cP
    cN
    cpc
    co
    #
    cle
    wbr
    #
    cN
    cc0
    @2
    cN
    cc0
    wceq
    #
    wa
    cc0
    cpnf
    @3
    cle
    0lepnf
    @5
    @2
    @3
    cP
    cc0
    cpc
    co
    #
    cpnf
    cN
    cc0
    cP
    cpc
    oveq2
    @0
    @6
    cpnf
    wceq
    @1
    cP
    pc0
    adantr
    sylan9eqr
    syl5breqr
    @0
    @1
    cN
    cc0
    wne
    #
    @4
    @0
    @1
    @7
    wa
    wa
    @3
    cP
    cN
    pczcl
    nn0ge0d
    anassrs
    pm2.61dane
end
