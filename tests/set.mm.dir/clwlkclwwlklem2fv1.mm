include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "ccnv.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "breq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "preq1d.mm"
include "ifbieq12d.mm"
include "elfzolt2.mm"
include "adantl.mm"
include "iftrued.mm"
include "sylan9eqr.mm"
include "cuz.mm"
include "wss.mm"
include "cz.mm"
include "cle.mm"
include "nn0z.mm"
include "2z.mm"
include "zsubcld.mm"
include "peano2zm.mm"
include "syl.mm"
include "1red.mm"
include "cr.mm"
include "2re.mm"
include "nn0re.mm"
include "1le2.mm"
include "lesub2dd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "sselda.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem clwlkclwwlklem2fv1
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cI: class I
  let cV: class V
  assume clwlkclwwlklem2.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> if ( x < ( ( # ` P ) - 2 ) , ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) , ( `' E ` { ( P ` x ) , ( P ` 0 ) } ) ) )

  disjoint P x
  disjoint E x
  disjoint I x
  disjoint V x
  assert |- ( ( ( # ` P ) e. NN0 /\ I e. ( 0 ..^ ( ( # ` P ) - 2 ) ) ) -> ( F ` I ) = ( `' E ` { ( P ` I ) , ( P ` ( I + 1 ) ) } ) )

  proof
    cP
    chash
    cfv
    #
    cn0
    wcel
    #
    cI
    cc0
    @0
    c2
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    vx
    cI
    vx
    cv
    #
    @2
    clt
    wbr
    #
    @6
    cP
    cfv
    #
    @6
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    ccnv
    #
    cfv
    #
    @8
    cc0
    cP
    cfv
    #
    cpr
    #
    @12
    cfv
    #
    cif
    #
    cI
    cP
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @12
    cfv
    #
    cc0
    @0
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cF
    cvv
    cF
    vx
    @24
    @17
    cmpt
    wceq
    @5
    clwlkclwwlklem2.f
    a1i
    @6
    cI
    wceq
    #
    @5
    @17
    cI
    @2
    clt
    wbr
    #
    @22
    @18
    @14
    cpr
    #
    @12
    cfv
    #
    cif
    @22
    @25
    @7
    @26
    @13
    @16
    @22
    @28
    @6
    cI
    @2
    clt
    breq1
    @25
    @11
    @21
    @12
    @25
    @8
    @18
    @10
    @20
    @6
    cI
    cP
    fveq2
    #
    @25
    @9
    @19
    cP
    @6
    cI
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    fveq2d
    @25
    @15
    @27
    @12
    @25
    @8
    @18
    @14
    @29
    preq1d
    fveq2d
    ifbieq12d
    @5
    @26
    @22
    @28
    @4
    @26
    @1
    cI
    cc0
    @2
    elfzolt2
    adantl
    iftrued
    sylan9eqr
    @1
    @3
    @24
    cI
    @1
    @23
    @2
    cuz
    cfv
    wcel
    #
    @3
    @24
    wss
    @1
    @2
    cz
    wcel
    @23
    cz
    wcel
    #
    @2
    @23
    cle
    wbr
    @30
    @1
    @0
    c2
    @0
    nn0z
    #
    c2
    cz
    wcel
    @1
    2z
    a1i
    zsubcld
    @1
    @0
    cz
    wcel
    @31
    @32
    @0
    peano2zm
    syl
    @1
    c1
    c2
    @0
    @1
    1red
    c2
    cr
    wcel
    @1
    2re
    a1i
    @0
    nn0re
    c1
    c2
    cle
    wbr
    @1
    1le2
    a1i
    lesub2dd
    @2
    @23
    eluz2
    syl3anbrc
    @2
    cc0
    @23
    fzoss2
    syl
    sselda
    @5
    @21
    @12
    fvexd
    fvmptd
end
