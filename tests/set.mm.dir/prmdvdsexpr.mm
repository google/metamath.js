include "cprime.mm"
include "wcel.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "wa.mm"
include "elnn0.mm"
include "w3a.mm"
include "prmdvdsexpb.mm"
include "biimpd.mm"
include "3expia.mm"
include "c1.mm"
include "prmnn.mm"
include "adantl.mm"
include "nncnd.mm"
include "exp0d.mm"
include "breq2d.mm"
include "nprmdvds1.mm"
include "pm2.21d.mm"
include "adantr.mm"
include "sylbid.mm"
include "oveq2.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem prmdvdsexpr
  let cP: class P
  let cQ: class Q
  let cN: class N


  assert |- ( ( P e. Prime /\ Q e. Prime /\ N e. NN0 ) -> ( P || ( Q ^ N ) -> P = Q ) )

  proof
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    cN
    cn0
    wcel
    #
    cP
    cQ
    cN
    cexp
    co
    #
    cdvds
    wbr
    #
    cP
    cQ
    wceq
    #
    wi
    #
    @2
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @0
    @1
    wa
    #
    @6
    cN
    elnn0
    @9
    @7
    @6
    @8
    @0
    @1
    @7
    @6
    @0
    @1
    @7
    w3a
    @4
    @5
    cP
    cQ
    cN
    prmdvdsexpb
    biimpd
    3expia
    @9
    @6
    @8
    cP
    cQ
    cc0
    cexp
    co
    #
    cdvds
    wbr
    #
    @5
    wi
    @9
    @11
    cP
    c1
    cdvds
    wbr
    #
    @5
    @9
    @10
    c1
    cP
    cdvds
    @9
    cQ
    @9
    cQ
    @1
    cQ
    cn
    wcel
    @0
    cQ
    prmnn
    adantl
    nncnd
    exp0d
    breq2d
    @0
    @12
    @5
    wi
    @1
    @0
    @12
    @5
    cP
    nprmdvds1
    pm2.21d
    adantr
    sylbid
    @8
    @4
    @11
    @5
    @8
    @3
    @10
    cP
    cdvds
    cN
    cc0
    cQ
    cexp
    oveq2
    breq2d
    imbi1d
    syl5ibrcom
    jaod
    syl5bi
    3impia
end
