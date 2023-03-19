include "cr.mm"
include "wcel.mm"
include "catan.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "atan0.mm"
include "0re.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "wne.mm"
include "cdm.mm"
include "cc.mm"
include "atanre.mm"
include "adantr.mm"
include "atancl.mm"
include "syl.mm"
include "ccj.mm"
include "cre.mm"
include "simpl.mm"
include "recnd.mm"
include "rere.mm"
include "eqnetrd.mm"
include "atancj.mm"
include "syl2anc.mm"
include "simprd.mm"
include "cjre.mm"
include "eqtrd.mm"
include "cjrebd.mm"
include "pm2.61dane.mm"

theorem atanrecl
  let cA: class A


  assert |- ( A e. RR -> ( arctan ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    catan
    cfv
    #
    cr
    wcel
    cA
    cc0
    @0
    cA
    cc0
    wceq
    #
    wa
    #
    @1
    cc0
    catan
    cfv
    #
    cr
    @3
    cA
    cc0
    catan
    @0
    @2
    simpr
    fveq2d
    @4
    cc0
    cr
    atan0
    0re
    eqeltri
    syl6eqel
    @0
    cA
    cc0
    wne
    #
    wa
    #
    @1
    @6
    cA
    catan
    cdm
    wcel
    #
    @1
    cc
    wcel
    @0
    @7
    @5
    cA
    atanre
    adantr
    cA
    atancl
    syl
    @6
    @1
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    catan
    cfv
    #
    @1
    @6
    @7
    @8
    @10
    wceq
    #
    @6
    cA
    cc
    wcel
    cA
    cre
    cfv
    #
    cc0
    wne
    @7
    @11
    wa
    @6
    cA
    @0
    @5
    simpl
    recnd
    @6
    @12
    cA
    cc0
    @0
    @12
    cA
    wceq
    @5
    cA
    rere
    adantr
    @0
    @5
    simpr
    eqnetrd
    cA
    atancj
    syl2anc
    simprd
    @6
    @9
    cA
    catan
    @0
    @9
    cA
    wceq
    @5
    cA
    cjre
    adantr
    fveq2d
    eqtrd
    cjrebd
    pm2.61dane
end
