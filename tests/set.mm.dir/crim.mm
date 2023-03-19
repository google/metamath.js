include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cim.mm"
include "cfv.mm"
include "cdiv.mm"
include "cre.mm"
include "cneg.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "syl2an.mm"
include "imval.mm"
include "syl.mm"
include "mpan.mm"
include "cc0.mm"
include "wne.mm"
include "ine0.mm"
include "divdir.mm"
include "3expa.mm"
include "mpanr12.mm"
include "sylan2.mm"
include "c1.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "irec.mm"
include "oveq1i.mm"
include "a1i.mm"
include "mulneg12.mm"
include "3eqtrd.mm"
include "divcan3.mm"
include "oveqan12d.mm"
include "negcl.mm"
include "addcom.mm"
include "sylan.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "id.mm"
include "renegcl.mm"
include "crre.mm"
include "syl2anr.mm"
include "3eqtr2d.mm"

theorem crim
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( Im ` ( A + ( _i x. B ) ) ) = B )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cim
    cfv
    #
    @4
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    cB
    ci
    cA
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    #
    cB
    @2
    @4
    cc
    wcel
    #
    @5
    @7
    wceq
    @0
    cA
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @12
    @1
    cA
    recn
    #
    @1
    ci
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @14
    ax-icn
    cB
    recn
    #
    ci
    cB
    mulcl
    #
    sylancr
    cA
    @3
    addcl
    syl2an
    @4
    imval
    syl
    @2
    @10
    @6
    cre
    @0
    @13
    @17
    @10
    @6
    wceq
    @1
    @15
    @18
    @13
    @17
    wa
    @6
    cA
    ci
    cdiv
    co
    #
    @3
    ci
    cdiv
    co
    #
    caddc
    co
    #
    @9
    cB
    caddc
    co
    #
    @10
    @17
    @13
    @14
    @6
    @22
    wceq
    #
    @16
    @17
    @14
    ax-icn
    @19
    mpan
    @13
    @14
    wa
    @16
    ci
    cc0
    wne
    #
    @24
    ax-icn
    ine0
    @13
    @14
    @16
    @25
    wa
    @24
    cA
    @3
    ci
    divdir
    3expa
    mpanr12
    sylan2
    @13
    @17
    @20
    @9
    @21
    cB
    caddc
    @13
    @20
    c1
    ci
    cdiv
    co
    #
    cA
    cmul
    co
    #
    ci
    cneg
    #
    cA
    cmul
    co
    #
    @9
    @13
    @16
    @25
    @20
    @27
    wceq
    ax-icn
    ine0
    cA
    ci
    divrec2
    mp3an23
    @27
    @29
    wceq
    @13
    @26
    @28
    cA
    cmul
    irec
    oveq1i
    a1i
    @16
    @13
    @29
    @9
    wceq
    ax-icn
    ci
    cA
    mulneg12
    mpan
    3eqtrd
    @17
    @16
    @25
    @21
    cB
    wceq
    ax-icn
    ine0
    cB
    ci
    divcan3
    mp3an23
    oveqan12d
    @13
    @9
    cc
    wcel
    #
    @17
    @23
    @10
    wceq
    @13
    @16
    @8
    cc
    wcel
    @30
    ax-icn
    cA
    negcl
    ci
    @8
    mulcl
    sylancr
    @9
    cB
    addcom
    sylan
    3eqtrrd
    syl2an
    fveq2d
    @1
    @1
    @8
    cr
    wcel
    @11
    cB
    wceq
    @0
    @1
    id
    cA
    renegcl
    cB
    @8
    crre
    syl2anr
    3eqtr2d
end
