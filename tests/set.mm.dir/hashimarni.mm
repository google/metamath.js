include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1.mm"
include "crn.mm"
include "cima.mm"
include "wceq.mm"
include "w3a.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "hashimarn.mm"
include "impcom.mm"
include "id.mm"
include "sylan9req.mm"
include "ex.mm"
include "adantr.mm"
include "sylbid.mm"
include "exp31.mm"
include "com23.mm"
include "com34.mm"
include "3imp.mm"
include "com12.mm"

theorem hashimarni
  let cP: class P
  let cE: class E
  let cF: class F
  let cN: class N
  let cV: class V


  assert |- ( ( E : dom E -1-1-> ran E /\ E e. V ) -> ( ( F : ( 0 ..^ ( # ` F ) ) -1-1-> dom E /\ P = ( E " ran F ) /\ ( # ` P ) = N ) -> ( # ` F ) = N ) )

  proof
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    cE
    cdm
    #
    cF
    wf1
    #
    cP
    cE
    cF
    crn
    cima
    #
    wceq
    #
    cP
    chash
    cfv
    #
    cN
    wceq
    #
    w3a
    @1
    cE
    crn
    cE
    wf1
    cE
    cV
    wcel
    wa
    #
    @0
    cN
    wceq
    #
    @2
    @4
    @6
    @7
    @8
    wi
    @2
    @4
    @7
    @6
    @8
    @2
    @7
    @4
    @6
    @8
    wi
    #
    @2
    @7
    @4
    @9
    @2
    @7
    wa
    #
    @4
    wa
    @6
    @3
    chash
    cfv
    #
    cN
    wceq
    #
    @8
    @4
    @6
    @12
    wb
    @10
    @4
    @5
    @11
    cN
    cP
    @3
    chash
    fveq2
    eqeq1d
    adantl
    @10
    @12
    @8
    wi
    @4
    @10
    @12
    @8
    @10
    @12
    @0
    @11
    cN
    @7
    @2
    @11
    @0
    wceq
    cE
    cF
    cV
    hashimarn
    impcom
    @12
    id
    sylan9req
    ex
    adantr
    sylbid
    exp31
    com23
    com34
    3imp
    com12
end
