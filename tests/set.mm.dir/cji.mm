include "ci.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "ccj.mm"
include "cneg.mm"
include "rei.mm"
include "c1.mm"
include "imi.mm"
include "oveq2i.mm"
include "ax-icn.mm"
include "mulid1i.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "remim.mm"
include "ax-mp.mm"
include "df-neg.mm"
include "3eqtr4i.mm"

theorem cji



  assert |- ( * ` _i ) = -u _i

  proof
    ci
    cre
    cfv
    #
    ci
    ci
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    ci
    cmin
    co
    ci
    ccj
    cfv
    #
    ci
    cneg
    @0
    cc0
    @2
    ci
    cmin
    rei
    @2
    ci
    c1
    cmul
    co
    ci
    @1
    c1
    ci
    cmul
    imi
    oveq2i
    ci
    ax-icn
    mulid1i
    eqtri
    oveq12i
    ci
    cc
    wcel
    @4
    @3
    wceq
    ax-icn
    ci
    remim
    ax-mp
    ci
    df-neg
    3eqtr4i
end
