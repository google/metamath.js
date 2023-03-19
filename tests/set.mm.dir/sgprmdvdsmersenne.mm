include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "cmo.mm"
include "co.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "c8.mm"
include "c7.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpll.mm"
include "simprr.mm"
include "oveq1.mm"
include "adantr.mm"
include "cz.mm"
include "prmz.mm"
include "mod42tp1mod8.mm"
include "sylan.mm"
include "sylan9eqr.mm"
include "simprl.mm"
include "sfprmdvdsmersenne.mm"
include "syl13anc.mm"

theorem sgprmdvdsmersenne
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( P e. Prime /\ ( P mod 4 ) = 3 ) /\ ( Q = ( ( 2 x. P ) + 1 ) /\ Q e. Prime ) ) -> Q || ( ( 2 ^ P ) - 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c4
    cmo
    co
    c3
    wceq
    #
    wa
    #
    cQ
    c2
    cP
    cmul
    co
    c1
    caddc
    co
    #
    wceq
    #
    cQ
    cprime
    wcel
    #
    wa
    #
    wa
    @0
    @5
    cQ
    c8
    cmo
    co
    #
    c7
    wceq
    @4
    cQ
    c2
    cP
    cexp
    co
    c1
    cmin
    co
    cdvds
    wbr
    @0
    @1
    @6
    simpll
    @2
    @4
    @5
    simprr
    @6
    @2
    @7
    @3
    c8
    cmo
    co
    #
    c7
    @4
    @7
    @8
    wceq
    @5
    cQ
    @3
    c8
    cmo
    oveq1
    adantr
    @0
    cP
    cz
    wcel
    @1
    @8
    c7
    wceq
    cP
    prmz
    cP
    mod42tp1mod8
    sylan
    sylan9eqr
    @2
    @4
    @5
    simprl
    cP
    cQ
    sfprmdvdsmersenne
    syl13anc
end
