include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cpc.mm"
include "cmin.mm"
include "cneg.mm"
include "wceq.mm"
include "cz.mm"
include "1z.mm"
include "zq.mm"
include "ax-mp.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "pcqdiv.mm"
include "mp3an2.mm"
include "pc1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "df-neg.mm"
include "syl6eqr.mm"

theorem pcrec
  let cA: class A
  let cP: class P
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z
  let cN: class N


  assert |- ( ( P e. Prime /\ ( A e. QQ /\ A =/= 0 ) ) -> ( P pCnt ( 1 / A ) ) = -u ( P pCnt A ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cq
    wcel
    cA
    cc0
    wne
    wa
    #
    wa
    #
    cP
    c1
    cA
    cdiv
    co
    cpc
    co
    #
    cc0
    cP
    cA
    cpc
    co
    #
    cmin
    co
    #
    @4
    cneg
    @2
    @3
    cP
    c1
    cpc
    co
    #
    @4
    cmin
    co
    #
    @5
    @0
    c1
    cq
    wcel
    #
    c1
    cc0
    wne
    #
    wa
    @1
    @3
    @7
    wceq
    @8
    @9
    c1
    cz
    wcel
    @8
    1z
    c1
    zq
    ax-mp
    ax-1ne0
    pm3.2i
    c1
    cA
    cP
    pcqdiv
    mp3an2
    @2
    @6
    cc0
    @4
    cmin
    @0
    @6
    cc0
    wceq
    @1
    cP
    pc1
    adantr
    oveq1d
    eqtrd
    @4
    df-neg
    syl6eqr
end
