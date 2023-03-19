include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cpi.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "ce.mm"
include "cfv.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "cneg.mm"
include "wceq.mm"
include "picn.mm"
include "subcl.mm"
include "mpan2.mm"
include "efival.mm"
include "syl.mm"
include "coscl.mm"
include "ax-icn.mm"
include "sincl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "negdid.mm"
include "cosmpi.mm"
include "sinmpi.mm"
include "oveq2d.mm"
include "mulneg2.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "negeqd.mm"

theorem efimpi
  let cA: class A


  assert |- ( A e. CC -> ( exp ` ( _i x. ( A - _pi ) ) ) = -u ( exp ` ( _i x. A ) ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cpi
    cmin
    co
    #
    cmul
    co
    ce
    cfv
    #
    cA
    ccos
    cfv
    #
    ci
    cA
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cneg
    #
    ci
    cA
    cmul
    co
    ce
    cfv
    #
    cneg
    @0
    @2
    @1
    ccos
    cfv
    #
    ci
    @1
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @7
    @0
    @1
    cc
    wcel
    #
    @2
    @12
    wceq
    @0
    cpi
    cc
    wcel
    @13
    picn
    cA
    cpi
    subcl
    mpan2
    @1
    efival
    syl
    @0
    @7
    @3
    cneg
    #
    @5
    cneg
    #
    caddc
    co
    @12
    @0
    @3
    @5
    cA
    coscl
    @0
    ci
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    ax-icn
    cA
    sincl
    #
    ci
    @4
    mulcl
    sylancr
    negdid
    @0
    @9
    @14
    @11
    @15
    caddc
    cA
    cosmpi
    @0
    @11
    ci
    @4
    cneg
    #
    cmul
    co
    #
    @15
    @0
    @10
    @19
    ci
    cmul
    cA
    sinmpi
    oveq2d
    @0
    @16
    @17
    @20
    @15
    wceq
    ax-icn
    @18
    ci
    @4
    mulneg2
    sylancr
    eqtrd
    oveq12d
    eqtr4d
    eqtr4d
    @0
    @8
    @6
    cA
    efival
    negeqd
    eqtr4d
end
