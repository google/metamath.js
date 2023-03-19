include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cdif.mm"
include "cif.mm"
include "co.mm"
include "wrex.mm"
include "simpll.mm"
include "wb.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ifbid.mm"
include "id.mm"
include "oveq12d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "eqidd.mm"
include "iftrued.mm"
include "wn.mm"
include "eldif.mm"
include "wo.mm"
include "wi.mm"
include "ianor.mm"
include "fveq1.mm"
include "elrab.mm"
include "xchnxbir.mm"
include "pm2.21.mm"
include "ax-1.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "ex.mm"

theorem symgmatr01lem
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vq: setvar q
  assume symgmatr01.p: |- P = ( Base ` ( SymGrp ` N ) )

  disjoint A k
  disjoint B k
  disjoint k q
  disjoint L k
  disjoint L q
  disjoint K k
  disjoint K q
  disjoint M k
  disjoint N k
  disjoint P k
  disjoint P q
  disjoint Q k
  disjoint Q q
  assert |- ( ( K e. N /\ L e. N ) -> ( Q e. ( P \ { q e. P | ( q ` K ) = L } ) -> E. k e. N if ( k = K , if ( ( Q ` k ) = L , A , B ) , ( k M ( Q ` k ) ) ) = B ) )

  proof
    cK
    cN
    wcel
    #
    cL
    cN
    wcel
    #
    wa
    #
    cQ
    cP
    cK
    vq
    cv
    #
    cfv
    #
    cL
    wceq
    #
    vq
    cP
    crab
    #
    cdif
    wcel
    #
    vk
    cv
    #
    cK
    wceq
    #
    @8
    cQ
    cfv
    #
    cL
    wceq
    #
    cA
    cB
    cif
    #
    @8
    @10
    cM
    co
    #
    cif
    #
    cB
    wceq
    #
    vk
    cN
    wrex
    @2
    @7
    wa
    #
    @15
    cK
    cK
    wceq
    #
    cK
    cQ
    cfv
    #
    cL
    wceq
    #
    cA
    cB
    cif
    #
    cK
    @18
    cM
    co
    #
    cif
    #
    cB
    wceq
    #
    vk
    cK
    cN
    @0
    @1
    @7
    simpll
    @9
    @15
    @23
    wb
    @16
    @9
    @14
    @22
    cB
    @9
    @9
    @17
    @12
    @13
    @20
    @21
    @8
    cK
    cK
    eqeq1
    @9
    @11
    @19
    cA
    cB
    @9
    @10
    @18
    cL
    @8
    cK
    cQ
    fveq2
    #
    eqeq1d
    ifbid
    @9
    @8
    cK
    @10
    @18
    cM
    @9
    id
    @24
    oveq12d
    ifbieq12d
    eqeq1d
    adantl
    @16
    @22
    @20
    cB
    @16
    @17
    @20
    @21
    @16
    cK
    eqidd
    iftrued
    @16
    @19
    cA
    cB
    @7
    @19
    wn
    #
    @2
    @7
    cQ
    cP
    wcel
    #
    cQ
    @6
    wcel
    #
    wn
    #
    wa
    @25
    cQ
    cP
    @6
    eldif
    @28
    @26
    @25
    @28
    @26
    wn
    #
    @25
    wo
    #
    @26
    @25
    wi
    #
    @26
    @19
    wa
    @30
    @27
    @26
    @19
    ianor
    @5
    @19
    vq
    cQ
    cP
    @3
    cQ
    wceq
    @4
    @18
    cL
    cK
    @3
    cQ
    fveq1
    eqeq1d
    elrab
    xchnxbir
    @29
    @31
    @25
    @26
    @25
    pm2.21
    @25
    @26
    ax-1
    jaoi
    sylbi
    impcom
    sylbi
    adantl
    iffalsed
    eqtrd
    rspcedvd
    ex
end
