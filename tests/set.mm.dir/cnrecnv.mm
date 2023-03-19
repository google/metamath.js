include "ccnv.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cre.mm"
include "cim.mm"
include "cop.mm"
include "wceq.mm"
include "wtru.mm"
include "cr.mm"
include "cxp.mm"
include "wf.mm"
include "wf1o.mm"
include "cnref1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "a1i.mm"
include "feqmptd.mm"
include "trud.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "df-ov.mm"
include "recl.mm"
include "imcl.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "replim.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "opelxpi.mm"
include "f1ocnvfv1.mm"
include "sylancr.mm"
include "eqtr3d.mm"
include "mpteq2ia.mm"
include "eqtri.mm"

theorem cnrecnv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assume cnrecnv.1: |- F = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) )

  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- `' F = ( z e. CC |-> <. ( Re ` z ) , ( Im ` z ) >. )

  proof
    cF
    ccnv
    #
    vz
    cc
    vz
    cv
    #
    @0
    cfv
    #
    cmpt
    #
    vz
    cc
    @1
    cre
    cfv
    #
    @1
    cim
    cfv
    #
    cop
    #
    cmpt
    @0
    @3
    wceq
    wtru
    vz
    cc
    cr
    cr
    cxp
    #
    @0
    cc
    @7
    @0
    wf
    #
    wtru
    @7
    cc
    cF
    wf1o
    #
    cc
    @7
    @0
    wf1o
    @8
    vx
    vy
    cF
    cnrecnv.1
    cnref1o
    #
    @7
    cc
    cF
    f1ocnv
    cc
    @7
    @0
    f1of
    mp2b
    a1i
    feqmptd
    trud
    vz
    cc
    @2
    @6
    @1
    cc
    wcel
    #
    @6
    cF
    cfv
    #
    @0
    cfv
    #
    @2
    @6
    @11
    @12
    @1
    @0
    @11
    @12
    @4
    ci
    @5
    cmul
    co
    #
    caddc
    co
    #
    @1
    @11
    @12
    @4
    @5
    cF
    co
    #
    @15
    @4
    @5
    cF
    df-ov
    @11
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @16
    @15
    wceq
    @1
    recl
    #
    @1
    imcl
    #
    vx
    vy
    @4
    @5
    cr
    cr
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    @15
    cF
    @4
    @23
    caddc
    co
    @21
    @4
    @23
    caddc
    oveq1
    @22
    @5
    wceq
    @23
    @14
    @4
    caddc
    @22
    @5
    ci
    cmul
    oveq2
    oveq2d
    cnrecnv.1
    @4
    @14
    caddc
    ovex
    ovmpt2
    syl2anc
    syl5eqr
    @1
    replim
    eqtr4d
    fveq2d
    @11
    @9
    @6
    @7
    wcel
    #
    @13
    @6
    wceq
    @10
    @11
    @17
    @18
    @24
    @19
    @20
    @4
    @5
    cr
    cr
    opelxpi
    syl2anc
    @7
    cc
    @6
    cF
    f1ocnvfv1
    sylancr
    eqtr3d
    mpteq2ia
    eqtri
end
