include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "ccrd.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "ccnv.mm"
include "fveq2.mm"
include "eqid.mm"
include "hashginv.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "hashgval.mm"
include "impbid.mm"
include "cdm.mm"
include "wb.mm"
include "finnum.mm"
include "carden2.mm"
include "syl2an.mm"
include "bitrd.mm"

theorem hashen
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cN: class N


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( ( # ` A ) = ( # ` B ) <-> A ~~ B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    wceq
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    wceq
    #
    cA
    cB
    cen
    wbr
    #
    @2
    @5
    @8
    @5
    @3
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    ccnv
    #
    cfv
    #
    @4
    @11
    cfv
    #
    wceq
    @2
    @8
    @3
    @4
    @11
    fveq2
    @0
    @1
    @12
    @6
    @13
    @7
    vx
    cA
    @10
    @10
    eqid
    #
    hashginv
    vx
    cB
    @10
    @14
    hashginv
    eqeqan12d
    syl5ib
    @8
    @6
    @10
    cfv
    #
    @7
    @10
    cfv
    #
    wceq
    @2
    @5
    @6
    @7
    @10
    fveq2
    @0
    @1
    @15
    @3
    @16
    @4
    vx
    cA
    @10
    @14
    hashgval
    vx
    cB
    @10
    @14
    hashgval
    eqeqan12d
    syl5ib
    impbid
    @0
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @17
    wcel
    @8
    @9
    wb
    @1
    cA
    finnum
    cB
    finnum
    cA
    cB
    carden2
    syl2an
    bitrd
end
