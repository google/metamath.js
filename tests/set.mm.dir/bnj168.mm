include "cv.mm"
include "c1o.mm"
include "wne.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "wceq.mm"
include "wex.mm"
include "wrex.mm"
include "com.mm"
include "c0.mm"
include "bnj158.mm"
include "anim2i.mm"
include "r19.42v.mm"
include "sylibr.mm"
include "neeq1.mm"
include "biimpac.mm"
include "df-1o.mm"
include "eqeq2i.mm"
include "con0.mm"
include "wb.mm"
include "nnon.mm"
include "0elon.mm"
include "suc11.mm"
include "sylancl.mm"
include "syl5rbb.mm"
include "necon3bid.mm"
include "syl5ibr.mm"
include "ancld.mm"
include "reximia.mm"
include "syl.mm"
include "anass.mm"
include "rexbii.mm"
include "sylib.mm"
include "simpr.mm"
include "bnj31.mm"
include "df-rex.mm"
include "csn.mm"
include "cdif.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitr2i.mm"
include "simprl.mm"
include "jca.mm"
include "eximi.mm"

theorem bnj168
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  assume bnj168.1: |- D = ( _om \ { (/) } )

  disjoint m n
  assert |- ( ( n =/= 1o /\ n e. D ) -> E. m e. D n = suc m )

  proof
    vn
    cv
    #
    c1o
    wne
    #
    @0
    cD
    wcel
    #
    wa
    #
    vm
    cv
    #
    cD
    wcel
    #
    @0
    @4
    csuc
    #
    wceq
    #
    wa
    #
    vm
    wex
    #
    @7
    vm
    cD
    wrex
    @3
    @4
    com
    wcel
    #
    @7
    @4
    c0
    wne
    #
    wa
    #
    wa
    #
    vm
    wex
    #
    @9
    @3
    @12
    vm
    com
    wrex
    @14
    @3
    @1
    @12
    wa
    #
    @12
    vm
    com
    @3
    @1
    @7
    wa
    #
    @11
    wa
    #
    vm
    com
    wrex
    #
    @15
    vm
    com
    wrex
    @3
    @16
    vm
    com
    wrex
    #
    @18
    @3
    @1
    @7
    vm
    com
    wrex
    #
    wa
    @19
    @2
    @20
    @1
    cD
    vn
    vm
    bnj168.1
    bnj158
    anim2i
    @1
    @7
    vm
    com
    r19.42v
    sylibr
    @16
    @17
    vm
    com
    @10
    @16
    @11
    @16
    @11
    @10
    @6
    c1o
    wne
    #
    @7
    @1
    @21
    @0
    @6
    c1o
    neeq1
    biimpac
    @10
    @4
    c0
    @6
    c1o
    @6
    c1o
    wceq
    @6
    c0
    csuc
    #
    wceq
    #
    @10
    @4
    c0
    wceq
    #
    c1o
    @22
    @6
    df-1o
    eqeq2i
    @10
    @4
    con0
    wcel
    c0
    con0
    wcel
    @23
    @24
    wb
    @4
    nnon
    0elon
    @4
    c0
    suc11
    sylancl
    syl5rbb
    necon3bid
    syl5ibr
    ancld
    reximia
    syl
    @17
    @15
    vm
    com
    @1
    @7
    @11
    anass
    rexbii
    sylib
    @1
    @12
    simpr
    bnj31
    @12
    vm
    com
    df-rex
    sylib
    @13
    @8
    vm
    @13
    @5
    @7
    @13
    @10
    @11
    wa
    #
    @5
    @12
    @11
    @10
    @7
    @11
    simpr
    anim2i
    @5
    @4
    com
    c0
    csn
    cdif
    #
    wcel
    @25
    cD
    @26
    @4
    bnj168.1
    eleq2i
    @4
    com
    c0
    eldifsn
    bitr2i
    sylib
    @10
    @7
    @11
    simprl
    jca
    eximi
    syl
    @7
    vm
    cD
    df-rex
    sylibr
end
