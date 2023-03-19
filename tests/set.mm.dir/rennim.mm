include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "crp.mm"
include "wn.mm"
include "wnel.mm"
include "cc0.mm"
include "wceq.mm"
include "cre.mm"
include "cfv.mm"
include "cc.mm"
include "wi.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "rpre.mm"
include "rereb.mm"
include "syl5ib.mm"
include "syl.mm"
include "caddc.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "0re.mm"
include "crre.mm"
include "mpan.mm"
include "eqtr3d.mm"
include "eqeq1d.mm"
include "sylibd.mm"
include "rpne0.mm"
include "necon2bi.mm"
include "eqcoms.mm"
include "syl6.mm"
include "pm2.01d.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem rennim
  let cA: class A


  assert |- ( A e. RR -> ( _i x. A ) e/ RR+ )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    #
    crp
    wcel
    #
    wn
    #
    @1
    crp
    wnel
    @0
    @2
    @0
    @2
    cc0
    @1
    wceq
    #
    @3
    @0
    @2
    @1
    cre
    cfv
    #
    @1
    wceq
    #
    @4
    @0
    @1
    cc
    wcel
    #
    @2
    @6
    wi
    @0
    ci
    cc
    wcel
    cA
    cc
    wcel
    @7
    ax-icn
    cA
    recn
    ci
    cA
    mulcl
    sylancr
    #
    @2
    @1
    cr
    wcel
    @7
    @6
    @1
    rpre
    @1
    rereb
    syl5ib
    syl
    @0
    @5
    cc0
    @1
    @0
    cc0
    @1
    caddc
    co
    #
    cre
    cfv
    #
    @5
    cc0
    @0
    @9
    @1
    cre
    @0
    @1
    @8
    addid2d
    fveq2d
    cc0
    cr
    wcel
    @0
    @10
    cc0
    wceq
    0re
    cc0
    cA
    crre
    mpan
    eqtr3d
    eqeq1d
    sylibd
    @3
    @1
    cc0
    @2
    @1
    cc0
    @1
    rpne0
    necon2bi
    eqcoms
    syl6
    pm2.01d
    @1
    crp
    df-nel
    sylibr
end
