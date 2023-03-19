include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cexp.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "efexp.mm"
include "sylan.mm"
include "zcn.mm"
include "mul12.mm"
include "mp3an2.mm"
include "fveq2d.mm"
include "efival.mm"
include "syl.mm"
include "eqtrd.mm"
include "ancoms.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "adantr.mm"
include "3eqtr3rd.mm"

theorem demoivre
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ N e. ZZ ) -> ( ( ( cos ` A ) + ( _i x. ( sin ` A ) ) ) ^ N ) = ( ( cos ` ( N x. A ) ) + ( _i x. ( sin ` ( N x. A ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cN
    ci
    cA
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    @2
    ce
    cfv
    #
    cN
    cexp
    co
    #
    cN
    cA
    cmul
    co
    #
    ccos
    cfv
    ci
    @7
    csin
    cfv
    cmul
    co
    caddc
    co
    #
    cA
    ccos
    cfv
    ci
    cA
    csin
    cfv
    cmul
    co
    caddc
    co
    #
    cN
    cexp
    co
    #
    @0
    @2
    cc
    wcel
    #
    @1
    @4
    @6
    wceq
    ci
    cc
    wcel
    #
    @0
    @11
    ax-icn
    ci
    cA
    mulcl
    mpan
    @2
    cN
    efexp
    sylan
    @1
    @0
    cN
    cc
    wcel
    #
    @4
    @8
    wceq
    #
    cN
    zcn
    @13
    @0
    @14
    @13
    @0
    wa
    #
    @4
    ci
    @7
    cmul
    co
    #
    ce
    cfv
    #
    @8
    @15
    @3
    @16
    ce
    @13
    @12
    @0
    @3
    @16
    wceq
    ax-icn
    cN
    ci
    cA
    mul12
    mp3an2
    fveq2d
    @15
    @7
    cc
    wcel
    @17
    @8
    wceq
    cN
    cA
    mulcl
    @7
    efival
    syl
    eqtrd
    ancoms
    sylan2
    @0
    @6
    @10
    wceq
    @1
    @0
    @5
    @9
    cN
    cexp
    cA
    efival
    oveq1d
    adantr
    3eqtr3rd
end
