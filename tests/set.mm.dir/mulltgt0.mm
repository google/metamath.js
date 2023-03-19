include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "renegcl.mm"
include "ad2antrr.mm"
include "lt0neg1.mm"
include "biimpa.mm"
include "adantr.mm"
include "simpr.mm"
include "mulgt0.mm"
include "syl21anc.mm"
include "cc.mm"
include "recn.mm"
include "ad2antrl.mm"
include "mulneg1d.mm"
include "breqtrd.mm"
include "remulcl.mm"
include "ad2ant2r.mm"
include "lt0neg1d.mm"
include "mpbird.mm"

theorem mulltgt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ A < 0 ) /\ ( B e. RR /\ 0 < B ) ) -> ( A x. B ) < 0 )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cc0
    clt
    wbr
    cc0
    @7
    cneg
    #
    clt
    wbr
    @6
    cc0
    cA
    cneg
    #
    cB
    cmul
    co
    #
    @8
    clt
    @6
    @9
    cr
    wcel
    #
    cc0
    @9
    clt
    wbr
    #
    @5
    cc0
    @10
    clt
    wbr
    @0
    @11
    @1
    @5
    cA
    renegcl
    ad2antrr
    @2
    @12
    @5
    @0
    @1
    @12
    cA
    lt0neg1
    biimpa
    adantr
    @2
    @5
    simpr
    @9
    cB
    mulgt0
    syl21anc
    @6
    cA
    cB
    @0
    cA
    cc
    wcel
    @1
    @5
    cA
    recn
    ad2antrr
    @3
    cB
    cc
    wcel
    @2
    @4
    cB
    recn
    ad2antrl
    mulneg1d
    breqtrd
    @6
    @7
    @0
    @3
    @7
    cr
    wcel
    @1
    @4
    cA
    cB
    remulcl
    ad2ant2r
    lt0neg1d
    mpbird
end
