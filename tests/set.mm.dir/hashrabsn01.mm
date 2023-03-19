include "csn.mm"
include "crab.mm"
include "wceq.mm"
include "c0.mm"
include "wo.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "wi.mm"
include "eqid.mm"
include "rabrsn.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "biimpi.mm"
include "hash0.mm"
include "syl6eq.mm"
include "orcd.mm"
include "syl6bi.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "hashsng.mm"
include "sylan9eqr.mm"
include "olcd.mm"
include "ex.mm"
include "wn.mm"
include "snprc.mm"
include "sylbi.mm"
include "pm2.61i.mm"
include "jaoi.mm"
include "mp2b.mm"

theorem hashrabsn01
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cN: class N

  disjoint A x
  assert |- ( ( # ` { x e. { A } | ph } ) = N -> ( N = 0 \/ N = 1 ) )

  proof
    wph
    vx
    cA
    csn
    #
    crab
    #
    @1
    wceq
    @1
    c0
    wceq
    #
    @1
    @0
    wceq
    #
    wo
    @1
    chash
    cfv
    #
    cN
    wceq
    #
    cN
    cc0
    wceq
    #
    cN
    c1
    wceq
    #
    wo
    #
    wi
    #
    @1
    eqid
    wph
    vx
    cA
    @1
    rabrsn
    @2
    @9
    @3
    @2
    @5
    c0
    chash
    cfv
    #
    cN
    wceq
    #
    @8
    @2
    @4
    @10
    cN
    @1
    c0
    chash
    fveq2
    eqeq1d
    @11
    @6
    @7
    @11
    cN
    @10
    cc0
    @11
    cN
    @10
    wceq
    @10
    cN
    eqcom
    biimpi
    hash0
    syl6eq
    orcd
    #
    syl6bi
    @3
    @5
    @0
    chash
    cfv
    #
    cN
    wceq
    #
    @8
    @3
    @4
    @13
    cN
    @1
    @0
    chash
    fveq2
    eqeq1d
    cA
    cvv
    wcel
    #
    @14
    @8
    wi
    #
    @15
    @14
    @8
    @15
    @14
    wa
    @7
    @6
    @14
    @15
    cN
    @13
    c1
    @14
    cN
    @13
    wceq
    @13
    cN
    eqcom
    biimpi
    cA
    cvv
    hashsng
    sylan9eqr
    olcd
    ex
    @15
    wn
    @0
    c0
    wceq
    #
    @16
    cA
    snprc
    @17
    @14
    @11
    @8
    @17
    @13
    @10
    cN
    @0
    c0
    chash
    fveq2
    eqeq1d
    @12
    syl6bi
    sylbi
    pm2.61i
    syl6bi
    jaoi
    mp2b
end
