include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cexp.mm"
include "cneg.mm"
include "peano2rem.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wa.mm"
include "df-neg.mm"
include "wb.mm"
include "0re.mm"
include "1re.mm"
include "lesub1.mm"
include "mp3an13.mm"
include "biimpa.mm"
include "syl5eqbr.mm"
include "3adant2.mm"
include "bernneq.mm"
include "syl3anc.mm"
include "wceq.mm"
include "cc.mm"
include "ax-1cn.mm"
include "recnd.mm"
include "nn0cn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "addcom.mm"
include "sylancr.mm"
include "3adant3.mm"
include "recn.mm"
include "pncan3.mm"
include "oveq1d.mm"
include "3brtr3d.mm"

theorem bernneq2
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. NN0 /\ 0 <_ A ) -> ( ( ( A - 1 ) x. N ) + 1 ) <_ ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    w3a
    #
    c1
    cA
    c1
    cmin
    co
    #
    cN
    cmul
    co
    #
    caddc
    co
    #
    c1
    @4
    caddc
    co
    #
    cN
    cexp
    co
    #
    @5
    c1
    caddc
    co
    #
    cA
    cN
    cexp
    co
    #
    cle
    @3
    @4
    cr
    wcel
    #
    @1
    c1
    cneg
    #
    @4
    cle
    wbr
    #
    @6
    @8
    cle
    wbr
    @0
    @1
    @11
    @2
    cA
    peano2rem
    #
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @13
    @1
    @0
    @2
    wa
    @12
    cc0
    c1
    cmin
    co
    #
    @4
    cle
    c1
    df-neg
    @0
    @2
    @15
    @4
    cle
    wbr
    #
    cc0
    cr
    wcel
    @0
    c1
    cr
    wcel
    @2
    @16
    wb
    0re
    1re
    cc0
    cA
    c1
    lesub1
    mp3an13
    biimpa
    syl5eqbr
    3adant2
    @4
    cN
    bernneq
    syl3anc
    @0
    @1
    @6
    @9
    wceq
    #
    @2
    @0
    @1
    wa
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @17
    ax-1cn
    @0
    @4
    cc
    wcel
    cN
    cc
    wcel
    @19
    @1
    @0
    @4
    @14
    recnd
    cN
    nn0cn
    @4
    cN
    mulcl
    syl2an
    c1
    @5
    addcom
    sylancr
    3adant3
    @0
    @1
    @8
    @10
    wceq
    @2
    @0
    @7
    cA
    cN
    cexp
    @0
    @18
    cA
    cc
    wcel
    @7
    cA
    wceq
    ax-1cn
    cA
    recn
    c1
    cA
    pncan3
    sylancr
    oveq1d
    3ad2ant1
    3brtr3d
end
