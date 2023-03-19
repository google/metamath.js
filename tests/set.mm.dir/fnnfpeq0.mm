include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wral.mm"
include "cdif.mm"
include "cdm.mm"
include "wn.mm"
include "rabeq0.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "fvresi.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "nne.mm"
include "syl6rbbr.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "fndifnfp.mm"
include "eqeq1d.mm"
include "fnresi.mm"
include "eqfnfv.mm"
include "mpan2.mm"
include "3bitr4d.mm"

theorem fnnfpeq0
  let cA: class A
  let cF: class F
  let vx: setvar x
  let cX: class X


  assert |- ( F Fn A -> ( dom ( F \ _I ) = (/) <-> F = ( _I |` A ) ) )

  proof
    cF
    cA
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    wne
    #
    vx
    cA
    crab
    #
    c0
    wceq
    #
    @2
    @1
    cid
    cA
    cres
    #
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    cF
    cid
    cdif
    cdm
    #
    c0
    wceq
    cF
    @6
    wceq
    #
    @5
    @3
    wn
    #
    vx
    cA
    wral
    @0
    @9
    @3
    vx
    cA
    rabeq0
    @0
    @12
    @8
    vx
    cA
    @0
    @1
    cA
    wcel
    #
    wa
    @8
    @2
    @1
    wceq
    #
    @12
    @13
    @8
    @14
    wb
    @0
    @13
    @7
    @1
    @2
    cA
    @1
    fvresi
    eqeq2d
    adantl
    @2
    @1
    nne
    syl6rbbr
    ralbidva
    syl5bb
    @0
    @10
    @4
    c0
    vx
    cA
    cF
    fndifnfp
    eqeq1d
    @0
    @6
    cA
    wfn
    @11
    @9
    wb
    cA
    fnresi
    vx
    cA
    cF
    @6
    eqfnfv
    mpan2
    3bitr4d
end
