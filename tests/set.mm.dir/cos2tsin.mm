include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "csin.mm"
include "cos2t.mm"
include "wceq.mm"
include "caddc.mm"
include "sincl.mm"
include "sqcld.mm"
include "coscl.mm"
include "2cn.mm"
include "adddi.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "sincossq.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "2t1e2.mm"
include "syl6eq.mm"
include "wb.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subadd.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "ax-1cn.mm"
include "sub32.mm"
include "mp3an13.mm"
include "syl.mm"
include "2m1e1.mm"
include "oveq1i.mm"
include "3eqtr2d.mm"

theorem cos2tsin
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( 2 x. A ) ) = ( 1 - ( 2 x. ( ( sin ` A ) ^ 2 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    c2
    cA
    cmul
    co
    ccos
    cfv
    c2
    cA
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    c1
    cmin
    co
    c2
    c2
    cA
    csin
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    cmin
    co
    #
    c1
    @6
    cmin
    co
    #
    cA
    cos2t
    @0
    @7
    @3
    c1
    cmin
    @0
    @7
    @3
    wceq
    #
    @6
    @3
    caddc
    co
    #
    c2
    wceq
    #
    @0
    @11
    c2
    c1
    cmul
    co
    #
    c2
    @0
    c2
    @5
    @2
    caddc
    co
    #
    cmul
    co
    #
    @11
    @13
    @0
    @5
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @15
    @11
    wceq
    #
    @0
    @4
    cA
    sincl
    sqcld
    #
    @0
    @1
    cA
    coscl
    sqcld
    #
    c2
    cc
    wcel
    #
    @16
    @17
    @18
    2cn
    c2
    @5
    @2
    adddi
    mp3an1
    syl2anc
    @0
    @14
    c1
    c2
    cmul
    cA
    sincossq
    oveq2d
    eqtr3d
    2t1e2
    syl6eq
    @0
    @6
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @10
    @12
    wb
    #
    @0
    @21
    @16
    @22
    2cn
    @19
    c2
    @5
    mulcl
    sylancr
    #
    @0
    @21
    @17
    @23
    2cn
    @20
    c2
    @2
    mulcl
    sylancr
    @21
    @22
    @23
    @24
    2cn
    c2
    @6
    @3
    subadd
    mp3an1
    syl2anc
    mpbird
    oveq1d
    @0
    @8
    c2
    c1
    cmin
    co
    #
    @6
    cmin
    co
    #
    @9
    @0
    @22
    @8
    @27
    wceq
    #
    @25
    @21
    @22
    c1
    cc
    wcel
    @28
    2cn
    ax-1cn
    c2
    @6
    c1
    sub32
    mp3an13
    syl
    @26
    c1
    @6
    cmin
    2m1e1
    oveq1i
    syl6eq
    3eqtr2d
end
