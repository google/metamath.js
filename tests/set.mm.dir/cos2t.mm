include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "coscl.mm"
include "sqcld.mm"
include "ax-1cn.mm"
include "subsub3.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "csin.mm"
include "cosadd.mm"
include "anidms.mm"
include "2times.mm"
include "fveq2d.mm"
include "sqvald.mm"
include "sincl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "addcomd.mm"
include "sincossq.mm"
include "eqtr3d.mm"
include "wb.mm"
include "subadd.mm"
include "mp3an1.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "2timesd.mm"
include "oveq1d.mm"

theorem cos2t
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( 2 x. A ) ) = ( ( 2 x. ( ( cos ` A ) ^ 2 ) ) - 1 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    c1
    @2
    cmin
    co
    #
    cmin
    co
    #
    @2
    @2
    caddc
    co
    #
    c1
    cmin
    co
    #
    c2
    cA
    cmul
    co
    #
    ccos
    cfv
    #
    c2
    @2
    cmul
    co
    #
    c1
    cmin
    co
    @0
    @2
    cc
    wcel
    #
    @10
    @4
    @6
    wceq
    #
    @0
    @1
    cA
    coscl
    #
    sqcld
    #
    @13
    @10
    c1
    cc
    wcel
    #
    @10
    @11
    ax-1cn
    @2
    c1
    @2
    subsub3
    mp3an2
    syl2anc
    @0
    @8
    @2
    cA
    csin
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    @4
    @0
    cA
    cA
    caddc
    co
    #
    ccos
    cfv
    #
    @1
    @1
    cmul
    co
    #
    @15
    @15
    cmul
    co
    #
    cmin
    co
    #
    @8
    @17
    @0
    @19
    @22
    wceq
    cA
    cA
    cosadd
    anidms
    @0
    @7
    @18
    ccos
    cA
    2times
    fveq2d
    @0
    @2
    @20
    @16
    @21
    cmin
    @0
    @1
    @12
    sqvald
    @0
    @15
    cA
    sincl
    #
    sqvald
    oveq12d
    3eqtr4d
    @0
    @3
    @16
    @2
    cmin
    @0
    @3
    @16
    wceq
    #
    @2
    @16
    caddc
    co
    #
    c1
    wceq
    #
    @0
    @16
    @2
    caddc
    co
    @25
    c1
    @0
    @16
    @2
    @0
    @15
    @23
    sqcld
    #
    @13
    addcomd
    cA
    sincossq
    eqtr3d
    @0
    @10
    @16
    cc
    wcel
    #
    @24
    @26
    wb
    #
    @13
    @27
    @14
    @10
    @28
    @29
    ax-1cn
    c1
    @2
    @16
    subadd
    mp3an1
    syl2anc
    mpbird
    oveq2d
    eqtr4d
    @0
    @9
    @5
    c1
    cmin
    @0
    @2
    @13
    2timesd
    oveq1d
    3eqtr4d
end
