include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "ci.mm"
include "cmin.mm"
include "cmul.mm"
include "wa.mm"
include "crio.mm"
include "cre.mm"
include "cim.mm"
include "cjval.mm"
include "wceq.mm"
include "replim.mm"
include "oveq1d.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ppncand.mm"
include "eqtrd.mm"
include "readdcld.mm"
include "eqeltrd.mm"
include "pnncand.mm"
include "a1i.mm"
include "adddid.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "mulass.mm"
include "mp3an12.mm"
include "syl.mm"
include "eqtr4d.mm"
include "c1.mm"
include "cneg.mm"
include "ixi.mm"
include "neg1rr.mm"
include "eqeltri.mm"
include "remulcl.mm"
include "wreu.mm"
include "wb.mm"
include "subcld.mm"
include "cju.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbi2and.mm"

theorem remim
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( * ` A ) = ( ( Re ` A ) - ( _i x. ( Im ` A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccj
    cfv
    cA
    vx
    cv
    #
    caddc
    co
    #
    cr
    wcel
    #
    ci
    cA
    @1
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    vx
    cc
    crio
    #
    cA
    cre
    cfv
    #
    ci
    cA
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    vx
    cA
    cjval
    @0
    cA
    @12
    caddc
    co
    #
    cr
    wcel
    #
    ci
    cA
    @12
    cmin
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    @8
    @12
    wceq
    #
    @0
    @13
    @9
    @9
    caddc
    co
    #
    cr
    @0
    @13
    @9
    @11
    caddc
    co
    #
    @12
    caddc
    co
    @19
    @0
    cA
    @20
    @12
    caddc
    cA
    replim
    #
    oveq1d
    @0
    @9
    @11
    @9
    @0
    @9
    cA
    recl
    #
    recnd
    #
    @0
    ci
    cc
    wcel
    #
    @10
    cc
    wcel
    @11
    cc
    wcel
    ax-icn
    @0
    @10
    cA
    imcl
    #
    recnd
    #
    ci
    @10
    mulcl
    sylancr
    #
    @23
    ppncand
    eqtrd
    @0
    @9
    @9
    @22
    @22
    readdcld
    eqeltrd
    @0
    @16
    ci
    ci
    cmul
    co
    #
    @10
    @10
    caddc
    co
    #
    cmul
    co
    #
    cr
    @0
    @16
    ci
    ci
    @29
    cmul
    co
    #
    cmul
    co
    #
    @30
    @0
    @15
    @31
    ci
    cmul
    @0
    @20
    @12
    cmin
    co
    @11
    @11
    caddc
    co
    @15
    @31
    @0
    @9
    @11
    @11
    @23
    @27
    @27
    pnncand
    @0
    cA
    @20
    @12
    cmin
    @21
    oveq1d
    @0
    ci
    @10
    @10
    @24
    @0
    ax-icn
    a1i
    @26
    @26
    adddid
    3eqtr4d
    oveq2d
    @0
    @29
    cc
    wcel
    #
    @30
    @32
    wceq
    #
    @0
    @29
    @0
    @10
    @10
    @25
    @25
    readdcld
    #
    recnd
    @24
    @24
    @33
    @34
    ax-icn
    ax-icn
    ci
    ci
    @29
    mulass
    mp3an12
    syl
    eqtr4d
    @0
    @28
    cr
    wcel
    @29
    cr
    wcel
    @30
    cr
    wcel
    @28
    c1
    cneg
    cr
    ixi
    neg1rr
    eqeltri
    @35
    @28
    @29
    remulcl
    sylancr
    eqeltrd
    @0
    @12
    cc
    wcel
    @7
    vx
    cc
    wreu
    @14
    @17
    wa
    #
    @18
    wb
    @0
    @9
    @11
    @23
    @27
    subcld
    vx
    cA
    cju
    @7
    @36
    vx
    cc
    @12
    @1
    @12
    wceq
    #
    @3
    @14
    @6
    @17
    @37
    @2
    @13
    cr
    @1
    @12
    cA
    caddc
    oveq2
    eleq1d
    @37
    @5
    @16
    cr
    @37
    @4
    @15
    ci
    cmul
    @1
    @12
    cA
    cmin
    oveq2
    oveq2d
    eleq1d
    anbi12d
    riota2
    syl2anc
    mpbi2and
    eqtrd
end
