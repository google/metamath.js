include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cre.mm"
include "ci.mm"
include "cim.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cr.mm"
include "cmin.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "negsubd.mm"
include "mulneg2.mm"
include "oveq2d.mm"
include "remim.mm"
include "3eqtr4rd.mm"
include "replim.mm"
include "eqeq12d.mm"
include "negcld.mm"
include "addcand.mm"
include "cc0.mm"
include "eqcom.mm"
include "eqnegd.mm"
include "syl5bb.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "ine0.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "mulcan.mm"
include "syl3anc.mm"
include "reim0b.mm"
include "3bitr4d.mm"
include "3bitrrd.mm"

theorem cjreb
  let cA: class A


  assert |- ( A e. CC -> ( A e. RR <-> ( * ` A ) = A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccj
    cfv
    #
    cA
    wceq
    cA
    cre
    cfv
    #
    ci
    cA
    cim
    cfv
    #
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    @2
    ci
    @3
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @5
    @7
    wceq
    #
    cA
    cr
    wcel
    #
    @0
    @1
    @6
    cA
    @8
    @0
    @2
    @7
    cneg
    #
    caddc
    co
    @2
    @7
    cmin
    co
    @6
    @1
    @0
    @2
    @7
    @0
    @2
    cA
    recl
    recnd
    #
    @0
    ci
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @7
    cc
    wcel
    ax-icn
    @0
    @3
    cA
    imcl
    recnd
    #
    ci
    @3
    mulcl
    sylancr
    #
    negsubd
    @0
    @5
    @11
    @2
    caddc
    @0
    @13
    @14
    @5
    @11
    wceq
    ax-icn
    @15
    ci
    @3
    mulneg2
    sylancr
    oveq2d
    cA
    remim
    3eqtr4rd
    cA
    replim
    eqeq12d
    @0
    @2
    @5
    @7
    @12
    @0
    @13
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    ax-icn
    @0
    @3
    @15
    negcld
    #
    ci
    @4
    mulcl
    sylancr
    @16
    addcand
    @0
    @4
    @3
    wceq
    #
    @3
    cc0
    wceq
    #
    @9
    @10
    @19
    @3
    @4
    wceq
    @0
    @20
    @4
    @3
    eqcom
    @0
    @3
    @15
    eqnegd
    syl5bb
    @0
    @17
    @14
    @13
    ci
    cc0
    wne
    #
    wa
    #
    @9
    @19
    wb
    @18
    @15
    @22
    @0
    @13
    @21
    ax-icn
    ine0
    pm3.2i
    a1i
    @4
    @3
    ci
    mulcan
    syl3anc
    cA
    reim0b
    3bitr4d
    3bitrrd
end
