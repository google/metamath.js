include "cc.mm"
include "wcel.mm"
include "casin.mm"
include "cfv.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "caddc.mm"
include "clog.mm"
include "cim.mm"
include "cpi.mm"
include "cdiv.mm"
include "cneg.mm"
include "cicc.mm"
include "asinval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "addcld.mm"
include "asinlem.mm"
include "logcld.mm"
include "imre.mm"
include "syl.mm"
include "eqtr4d.mm"
include "cc0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "asinlem3.mm"
include "argrege0.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem asinbnd
  let cA: class A


  assert |- ( A e. CC -> ( Re ` ( arcsin ` A ) ) e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    casin
    cfv
    #
    cre
    cfv
    #
    ci
    cA
    cmul
    co
    #
    c1
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    @10
    cicc
    co
    #
    @0
    @2
    ci
    cneg
    @8
    cmul
    co
    #
    cre
    cfv
    #
    @9
    @0
    @1
    @12
    cre
    cA
    asinval
    fveq2d
    @0
    @8
    cc
    wcel
    @9
    @13
    wceq
    @0
    @7
    @0
    @3
    @6
    ci
    cc
    wcel
    @0
    @3
    cc
    wcel
    ax-icn
    ci
    cA
    mulcl
    mpan
    @0
    @5
    @0
    c1
    cc
    wcel
    @4
    cc
    wcel
    @5
    cc
    wcel
    ax-1cn
    cA
    sqcl
    c1
    @4
    subcl
    sylancr
    sqrtcld
    addcld
    #
    cA
    asinlem
    #
    logcld
    @8
    imre
    syl
    eqtr4d
    @0
    @7
    cc
    wcel
    @7
    cc0
    wne
    cc0
    @7
    cre
    cfv
    cle
    wbr
    @9
    @11
    wcel
    @14
    @15
    cA
    asinlem3
    @7
    argrege0
    syl3anc
    eqeltrd
end
