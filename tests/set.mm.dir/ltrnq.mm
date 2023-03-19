include "cltq.mm"
include "wbr.mm"
include "cnq.mm"
include "wcel.mm"
include "wa.mm"
include "crq.mm"
include "cfv.mm"
include "ltrelnq.mm"
include "brel.mm"
include "dmrecnq.mm"
include "0nnq.mm"
include "ndmfvrcl.mm"
include "anim12ci.mm"
include "syl.mm"
include "cv.mm"
include "wb.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq1d.mm"
include "cmq.mm"
include "co.mm"
include "recclnq.mm"
include "mulclnq.mm"
include "syl2an.mm"
include "ltmnq.mm"
include "mulcomnq.mm"
include "mulassnq.mm"
include "3eqtr2i.mm"
include "c1q.mm"
include "recidnq.mm"
include "oveq2d.mm"
include "mulidnq.mm"
include "sylan9eq.mm"
include "syl5eq.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "sylan9eqr.mm"
include "breq12d.mm"
include "bitrd.mm"
include "vtocl2ga.mm"
include "pm5.21nii.mm"

theorem ltrnq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A <Q B <-> ( *Q ` B ) <Q ( *Q ` A ) )

  proof
    cA
    cB
    cltq
    wbr
    #
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    wa
    #
    cB
    crq
    cfv
    #
    cA
    crq
    cfv
    #
    cltq
    wbr
    #
    cA
    cB
    cnq
    cnq
    cltq
    ltrelnq
    brel
    @6
    @4
    cnq
    wcel
    #
    @5
    cnq
    wcel
    #
    wa
    @3
    @4
    @5
    cnq
    cnq
    cltq
    ltrelnq
    brel
    @7
    @2
    @8
    @1
    cB
    cnq
    crq
    dmrecnq
    0nnq
    ndmfvrcl
    cA
    cnq
    crq
    dmrecnq
    0nnq
    ndmfvrcl
    anim12ci
    syl
    vx
    cv
    #
    vy
    cv
    #
    cltq
    wbr
    #
    @10
    crq
    cfv
    #
    @9
    crq
    cfv
    #
    cltq
    wbr
    #
    wb
    cA
    @10
    cltq
    wbr
    #
    @12
    @5
    cltq
    wbr
    #
    wb
    @0
    @6
    wb
    vx
    vy
    cA
    cB
    cnq
    cnq
    @9
    cA
    wceq
    #
    @11
    @15
    @14
    @16
    @9
    cA
    @10
    cltq
    breq1
    @17
    @13
    @5
    @12
    cltq
    @9
    cA
    crq
    fveq2
    breq2d
    bibi12d
    @10
    cB
    wceq
    #
    @15
    @0
    @16
    @6
    @10
    cB
    cA
    cltq
    breq2
    @18
    @12
    @4
    @5
    cltq
    @10
    cB
    crq
    fveq2
    breq1d
    bibi12d
    @9
    cnq
    wcel
    #
    @10
    cnq
    wcel
    #
    wa
    #
    @11
    @13
    @12
    cmq
    co
    #
    @9
    cmq
    co
    #
    @22
    @10
    cmq
    co
    #
    cltq
    wbr
    #
    @14
    @21
    @22
    cnq
    wcel
    #
    @11
    @25
    wb
    @19
    @13
    cnq
    wcel
    #
    @12
    cnq
    wcel
    #
    @26
    @20
    @9
    recclnq
    #
    @10
    recclnq
    #
    @13
    @12
    mulclnq
    syl2an
    @9
    @10
    @22
    ltmnq
    syl
    @21
    @23
    @12
    @24
    @13
    cltq
    @21
    @23
    @12
    @9
    @13
    cmq
    co
    #
    cmq
    co
    #
    @12
    @23
    @9
    @22
    cmq
    co
    @31
    @12
    cmq
    co
    @32
    @22
    @9
    mulcomnq
    @9
    @13
    @12
    mulassnq
    @31
    @12
    mulcomnq
    3eqtr2i
    @19
    @20
    @32
    @12
    c1q
    cmq
    co
    #
    @12
    @19
    @31
    c1q
    @12
    cmq
    @9
    recidnq
    oveq2d
    @20
    @28
    @33
    @12
    wceq
    @30
    @12
    mulidnq
    syl
    sylan9eq
    syl5eq
    @21
    @24
    @13
    @10
    @12
    cmq
    co
    #
    cmq
    co
    #
    @13
    @24
    @13
    @12
    @10
    cmq
    co
    #
    cmq
    co
    @35
    @13
    @12
    @10
    mulassnq
    @36
    @34
    @13
    cmq
    @12
    @10
    mulcomnq
    oveq2i
    eqtri
    @20
    @19
    @35
    @13
    c1q
    cmq
    co
    #
    @13
    @20
    @34
    c1q
    @13
    cmq
    @10
    recidnq
    oveq2d
    @19
    @27
    @37
    @13
    wceq
    @29
    @13
    mulidnq
    syl
    sylan9eqr
    syl5eq
    breq12d
    bitrd
    vtocl2ga
    pm5.21nii
end
