include "cfn.mm"
include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "cn0.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "chash.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "hashcl.mm"
include "isfinite4.mm"
include "biimpi.mm"
include "jca.mm"
include "wceq.mm"
include "eleq1.mm"
include "oveq2.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "df-rex.mm"
include "sylibr.mm"
include "hasheni.mm"
include "eqcomd.mm"
include "hashfz1.mm"
include "ovex.mm"
include "eqtr.mm"
include "eqeng.mm"
include "syl5.mm"
include "syl2anr.mm"
include "entr.mm"
include "sylancom.mm"
include "rexlimiva.mm"
include "impbii.mm"

theorem rp-isfinite5
  let cA: class A
  let vn: setvar n

  disjoint A n
  assert |- ( A e. Fin <-> E. n e. NN0 ( 1 ... n ) ~~ A )

  proof
    cA
    cfn
    wcel
    #
    c1
    vn
    cv
    #
    cfz
    co
    #
    cA
    cen
    wbr
    #
    vn
    cn0
    wrex
    #
    @0
    @1
    cn0
    wcel
    #
    @3
    wa
    #
    vn
    wex
    #
    @4
    cA
    chash
    cfv
    #
    cvv
    wcel
    @0
    @8
    cn0
    wcel
    #
    c1
    @8
    cfz
    co
    #
    cA
    cen
    wbr
    #
    wa
    #
    @7
    cA
    chash
    fvex
    @0
    @9
    @11
    cA
    hashcl
    @0
    @11
    cA
    isfinite4
    #
    biimpi
    jca
    @6
    @12
    vn
    @8
    cvv
    @1
    @8
    wceq
    #
    @5
    @9
    @3
    @11
    @1
    @8
    cn0
    eleq1
    @14
    @2
    @10
    cA
    cen
    @1
    @8
    c1
    cfz
    oveq2
    breq1d
    anbi12d
    spcegv
    mpsyl
    @3
    vn
    cn0
    df-rex
    sylibr
    @3
    @0
    vn
    cn0
    @6
    @11
    @0
    @5
    @3
    @10
    @2
    cen
    wbr
    #
    @11
    @3
    @8
    @2
    chash
    cfv
    #
    wceq
    #
    @16
    @1
    wceq
    #
    @15
    @5
    @3
    @16
    @8
    @2
    cA
    hasheni
    eqcomd
    @1
    hashfz1
    @10
    cvv
    wcel
    #
    @17
    @18
    wa
    @8
    @1
    wceq
    #
    @15
    c1
    @8
    cfz
    ovex
    @8
    @16
    @1
    eqtr
    @20
    @10
    @2
    wceq
    @19
    @15
    @8
    @1
    c1
    cfz
    oveq2
    @10
    @2
    cvv
    eqeng
    syl5
    mpsyl
    syl2anr
    @10
    @2
    cA
    entr
    sylancom
    @13
    sylibr
    rexlimiva
    impbii
end
