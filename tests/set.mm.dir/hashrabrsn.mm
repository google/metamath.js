include "csn.mm"
include "crab.mm"
include "wceq.mm"
include "c0.mm"
include "wo.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "eqid.mm"
include "rabrsn.mm"
include "fveq2.mm"
include "cc0.mm"
include "hash0.mm"
include "0nn0.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "cvv.mm"
include "c1.mm"
include "hashsng.mm"
include "1nn0.mm"
include "wn.mm"
include "snprc.mm"
include "sylbi.mm"
include "pm2.61i.mm"
include "jaoi.mm"
include "mp2b.mm"

theorem hashrabrsn
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( # ` { x e. { A } | ph } ) e. NN0

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
    cn0
    wcel
    #
    @1
    eqid
    wph
    vx
    cA
    @1
    rabrsn
    @2
    @5
    @3
    @2
    @4
    c0
    chash
    cfv
    #
    cn0
    @1
    c0
    chash
    fveq2
    @6
    cc0
    cn0
    hash0
    0nn0
    eqeltri
    #
    syl6eqel
    @3
    @4
    @0
    chash
    cfv
    #
    cn0
    @1
    @0
    chash
    fveq2
    cA
    cvv
    wcel
    #
    @8
    cn0
    wcel
    #
    @9
    @8
    c1
    cn0
    cA
    cvv
    hashsng
    1nn0
    syl6eqel
    @9
    wn
    @0
    c0
    wceq
    #
    @10
    cA
    snprc
    @11
    @8
    @6
    cn0
    @0
    c0
    chash
    fveq2
    @7
    syl6eqel
    sylbi
    pm2.61i
    syl6eqel
    jaoi
    mp2b
end
