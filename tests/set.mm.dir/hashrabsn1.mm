include "csn.mm"
include "crab.mm"
include "wceq.mm"
include "c0.mm"
include "wo.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wsbc.mm"
include "wi.mm"
include "eqid.mm"
include "rabrsn.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cc0.mm"
include "hash0.mm"
include "eqeq1i.mm"
include "wne.mm"
include "0ne1.mm"
include "eqneqall.mm"
include "mpi.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "snidg.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "mpbird.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "simprbi.mm"
include "syl.mm"
include "a1d.mm"
include "ex.mm"
include "wn.mm"
include "snprc.mm"
include "eqeq2.mm"
include "ax-1ne0.mm"
include "eqcoms.mm"
include "pm2.61i.mm"
include "jaoi.mm"
include "mp2b.mm"

theorem hashrabsn1
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( # ` { x e. { A } | ph } ) = 1 -> [. A / x ]. ph )

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
    c1
    wceq
    #
    wph
    vx
    cA
    wsbc
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
    @7
    @3
    @2
    @5
    c0
    chash
    cfv
    #
    c1
    wceq
    #
    @6
    @2
    @4
    @8
    c1
    @1
    c0
    chash
    fveq2
    eqeq1d
    #
    @9
    cc0
    c1
    wceq
    #
    @6
    @8
    cc0
    c1
    hash0
    eqeq1i
    #
    @11
    cc0
    c1
    wne
    @6
    0ne1
    @6
    cc0
    c1
    eqneqall
    mpi
    sylbi
    syl6bi
    cA
    cvv
    wcel
    #
    @3
    @7
    wi
    #
    @13
    @3
    @7
    @13
    @3
    wa
    #
    @6
    @5
    @15
    cA
    @1
    wcel
    #
    @6
    @15
    @16
    cA
    @0
    wcel
    #
    @13
    @17
    @3
    cA
    cvv
    snidg
    adantr
    @3
    @16
    @17
    wb
    @13
    @1
    @0
    cA
    eleq2
    adantl
    mpbird
    @16
    @17
    @6
    wph
    vx
    cA
    @0
    vx
    @0
    nfcv
    elrabsf
    simprbi
    syl
    a1d
    ex
    @13
    wn
    @0
    c0
    wceq
    #
    @14
    cA
    snprc
    @18
    @3
    @2
    @7
    @0
    c0
    @1
    eqeq2
    @2
    @5
    @9
    @6
    @10
    @9
    @11
    @6
    @12
    @6
    c1
    cc0
    c1
    cc0
    wceq
    c1
    cc0
    wne
    @6
    ax-1ne0
    @6
    c1
    cc0
    eqneqall
    mpi
    eqcoms
    sylbi
    syl6bi
    syl6bi
    sylbi
    pm2.61i
    jaoi
    mp2b
end
