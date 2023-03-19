include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cxr.mm"
include "cc0.mm"
include "wceq.mm"
include "cpnf.mm"
include "pc0.mm"
include "pnfxr.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "pcqcl.mm"
include "zred.mm"
include "rexrd.mm"
include "expr.mm"
include "pm2.61dne.mm"

theorem pcxcl
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ N e. QQ ) -> ( P pCnt N ) e. RR* )

  proof
    cP
    cprime
    wcel
    #
    cN
    cq
    wcel
    #
    wa
    #
    cP
    cN
    cpc
    co
    #
    cxr
    wcel
    #
    cN
    cc0
    @2
    @4
    cN
    cc0
    wceq
    #
    cP
    cc0
    cpc
    co
    #
    cxr
    wcel
    #
    @0
    @7
    @1
    @0
    @6
    cpnf
    cxr
    cP
    pc0
    pnfxr
    syl6eqel
    adantr
    @5
    @3
    @6
    cxr
    cN
    cc0
    cP
    cpc
    oveq2
    eleq1d
    syl5ibrcom
    @0
    @1
    cN
    cc0
    wne
    #
    @4
    @0
    @1
    @8
    wa
    wa
    #
    @3
    @9
    @3
    cP
    cN
    pcqcl
    zred
    rexrd
    expr
    pm2.61dne
end
