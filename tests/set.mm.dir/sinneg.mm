include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "csin.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "wceq.mm"
include "negcl.mm"
include "sinval.mm"
include "syl.mm"
include "negeqd.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "efcl.mm"
include "negicn.mm"
include "subcld.mm"
include "cc0.mm"
include "wne.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "divneg.mm"
include "mp3an23.mm"
include "eqtrd.mm"
include "mulneg12.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "mul2neg.mm"
include "oveq12d.mm"
include "negsubdi2d.mm"
include "eqtr4d.mm"
include "oveq1d.mm"

theorem sinneg
  let cA: class A


  assert |- ( A e. CC -> ( sin ` -u A ) = -u ( sin ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    csin
    cfv
    #
    ci
    @1
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @1
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    cA
    csin
    cfv
    #
    cneg
    #
    @0
    @1
    cc
    wcel
    @2
    @10
    wceq
    cA
    negcl
    @1
    sinval
    syl
    @0
    @12
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    @5
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    #
    cneg
    #
    @9
    cdiv
    co
    #
    @10
    @0
    @12
    @17
    @9
    cdiv
    co
    #
    cneg
    #
    @19
    @0
    @11
    @20
    cA
    sinval
    negeqd
    @0
    @17
    cc
    wcel
    #
    @21
    @19
    wceq
    #
    @0
    @14
    @16
    @0
    @13
    cc
    wcel
    #
    @14
    cc
    wcel
    ci
    cc
    wcel
    #
    @0
    @24
    ax-icn
    ci
    cA
    mulcl
    mpan
    @13
    efcl
    syl
    #
    @0
    @15
    cc
    wcel
    #
    @16
    cc
    wcel
    @5
    cc
    wcel
    @0
    @27
    negicn
    @5
    cA
    mulcl
    mpan
    @15
    efcl
    syl
    #
    subcld
    @22
    @9
    cc
    wcel
    @9
    cc0
    wne
    @23
    2mulicn
    2muline0
    @17
    @9
    divneg
    mp3an23
    syl
    eqtrd
    @0
    @8
    @18
    @9
    cdiv
    @0
    @8
    @16
    @14
    cmin
    co
    @18
    @0
    @4
    @16
    @7
    @14
    cmin
    @0
    @3
    @15
    ce
    @0
    @15
    @3
    @25
    @0
    @15
    @3
    wceq
    ax-icn
    ci
    cA
    mulneg12
    mpan
    eqcomd
    fveq2d
    @0
    @6
    @13
    ce
    @25
    @0
    @6
    @13
    wceq
    ax-icn
    ci
    cA
    mul2neg
    mpan
    fveq2d
    oveq12d
    @0
    @14
    @16
    @26
    @28
    negsubdi2d
    eqtr4d
    oveq1d
    eqtr4d
    eqtr4d
end
