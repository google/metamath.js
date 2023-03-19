include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "ccos.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cc0.mm"
include "cosatan.mm"
include "cc.mm"
include "ax-1cn.mm"
include "wne.mm"
include "atandm4.mm"
include "simplbi.mm"
include "sqcld.mm"
include "addcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "sqsqrtd.mm"
include "simprbi.mm"
include "eqnetrd.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "mpbid.mm"
include "recne0d.mm"

theorem cosatanne0
  let cA: class A


  assert |- ( A e. dom arctan -> ( cos ` ( arctan ` A ) ) =/= 0 )

  proof
    cA
    catan
    cdm
    wcel
    #
    cA
    catan
    cfv
    ccos
    cfv
    c1
    c1
    cA
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    cc0
    cA
    cosatan
    @0
    @3
    @0
    @2
    @0
    c1
    cc
    wcel
    @1
    cc
    wcel
    @2
    cc
    wcel
    ax-1cn
    @0
    cA
    @0
    cA
    cc
    wcel
    #
    @2
    cc0
    wne
    #
    cA
    atandm4
    #
    simplbi
    sqcld
    c1
    @1
    addcl
    sylancr
    #
    sqrtcld
    #
    @0
    @3
    c2
    cexp
    co
    #
    cc0
    wne
    #
    @3
    cc0
    wne
    #
    @0
    @9
    @2
    cc0
    @0
    @2
    @7
    sqsqrtd
    @0
    @4
    @5
    @6
    simprbi
    eqnetrd
    @0
    @3
    cc
    wcel
    @10
    @11
    wb
    @8
    @3
    sqne0
    syl
    mpbid
    recne0d
    eqnetrd
end
