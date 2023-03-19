include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cnzr.mm"
include "wn.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "wceq.mm"
include "crg.mm"
include "wi.mm"
include "eqid.mm"
include "lmodring.mm"
include "chash.mm"
include "c1.mm"
include "0ringnnzr.mm"
include "wa.mm"
include "cur.mm"
include "0ring01eq.mm"
include "cv.mm"
include "wral.mm"
include "cvsca.mm"
include "co.mm"
include "lmodvs1.mm"
include "eqcom.mm"
include "biimpi.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "lmod0vs.mm"
include "sylan9eqr.mm"
include "sylan9eq.mm"
include "exp32.mm"
include "mpcom.mm"
include "com12.mm"
include "impl.mm"
include "ralrimiva.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "lmodbn0.mm"
include "eqsn.mm"
include "syl.mm"
include "adantl.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbird.mm"
include "com23.mm"
include "imp.mm"

theorem lmod0rng
  let cM: class M
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. LMod /\ -. ( Scalar ` M ) e. NzRing ) -> ( Base ` M ) = { ( 0g ` M ) } )

  proof
    cM
    clmod
    wcel
    #
    cM
    csca
    cfv
    #
    cnzr
    wcel
    wn
    #
    cM
    cbs
    cfv
    #
    cM
    c0g
    cfv
    #
    csn
    wceq
    #
    @1
    crg
    wcel
    #
    @0
    @2
    @5
    wi
    @1
    cM
    @1
    eqid
    #
    lmodring
    @6
    @2
    @0
    @5
    @6
    @2
    @1
    cbs
    cfv
    #
    chash
    cfv
    c1
    wceq
    #
    @0
    @5
    wi
    #
    @1
    0ringnnzr
    @6
    @9
    @10
    @6
    @9
    wa
    @1
    c0g
    cfv
    #
    @1
    cur
    cfv
    #
    wceq
    #
    @10
    @8
    @1
    @12
    @11
    @8
    eqid
    @11
    eqid
    #
    @12
    eqid
    #
    0ring01eq
    @13
    @0
    @5
    @13
    @0
    wa
    #
    @5
    vv
    cv
    #
    @4
    wceq
    #
    vv
    @3
    wral
    #
    @16
    @18
    vv
    @3
    @13
    @0
    @17
    @3
    wcel
    #
    @18
    @0
    @20
    wa
    #
    @13
    @18
    @12
    @17
    cM
    cvsca
    cfv
    #
    co
    #
    @17
    wceq
    #
    @21
    @13
    @18
    wi
    @22
    @12
    @1
    @3
    cM
    @17
    @3
    eqid
    #
    @7
    @22
    eqid
    #
    @15
    lmodvs1
    @24
    @21
    @13
    @18
    @24
    @21
    @13
    wa
    @17
    @23
    @4
    @24
    @17
    @23
    wceq
    @23
    @17
    eqcom
    biimpi
    @13
    @21
    @23
    @11
    @17
    @22
    co
    #
    @4
    @23
    @27
    wceq
    @12
    @11
    @12
    @11
    @17
    @22
    oveq1
    eqcoms
    @22
    @1
    @11
    @3
    cM
    @17
    @4
    @25
    @7
    @26
    @14
    @4
    eqid
    lmod0vs
    sylan9eqr
    sylan9eq
    exp32
    mpcom
    com12
    impl
    ralrimiva
    @0
    @5
    @19
    wb
    #
    @13
    @0
    @3
    c0
    wne
    @28
    @3
    cM
    @25
    lmodbn0
    vv
    @3
    @4
    eqsn
    syl
    adantl
    mpbird
    ex
    syl
    ex
    sylbird
    com23
    mpcom
    imp
end
