include "cc.mm"
include "wcel.mm"
include "csinh.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cdiv.mm"
include "c1.mm"
include "cneg.mm"
include "sinhval-named.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "sincld.mm"
include "cc0.mm"
include "wne.mm"
include "ine0.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "syl.mm"
include "irec.mm"
include "oveq1i.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem sinh-conventional
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. CC -> ( sinh ` A ) = ( -u _i x. ( sin ` ( _i x. A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csinh
    cfv
    ci
    cA
    cmul
    co
    #
    csin
    cfv
    #
    ci
    cdiv
    co
    #
    c1
    ci
    cdiv
    co
    #
    @2
    cmul
    co
    #
    ci
    cneg
    #
    @2
    cmul
    co
    #
    cA
    sinhval-named
    @0
    @2
    cc
    wcel
    #
    @3
    @5
    wceq
    #
    @0
    @1
    ci
    cc
    wcel
    #
    @0
    @1
    cc
    wcel
    ax-icn
    ci
    cA
    mulcl
    mpan
    sincld
    @8
    @10
    ci
    cc0
    wne
    @9
    ax-icn
    ine0
    @2
    ci
    divrec2
    mp3an23
    syl
    @5
    @7
    wceq
    @0
    @4
    @6
    @2
    cmul
    irec
    oveq1i
    a1i
    3eqtrd
end
