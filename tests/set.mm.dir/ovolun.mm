include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "crp.mm"
include "wral.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "ovolunlem2.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "wb.mm"
include "unss.mm"
include "biimpi.mm"
include "ad2ant2r.mm"
include "ovolcl.mm"
include "syl.mm"
include "readdcl.mm"
include "ad2ant2l.mm"
include "xralrple.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem ovolun
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( ( A C_ RR /\ ( vol* ` A ) e. RR ) /\ ( B C_ RR /\ ( vol* ` B ) e. RR ) ) -> ( vol* ` ( A u. B ) ) <_ ( ( vol* ` A ) + ( vol* ` B ) ) )

  proof
    cA
    cr
    wss
    #
    cA
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cun
    #
    covol
    cfv
    #
    @1
    @5
    caddc
    co
    #
    cle
    wbr
    #
    @10
    @11
    vx
    cv
    #
    caddc
    co
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @8
    @14
    vx
    crp
    @8
    @13
    crp
    wcel
    #
    wa
    cA
    cB
    @13
    @3
    @7
    @16
    simpll
    @3
    @7
    @16
    simplr
    @8
    @16
    simpr
    ovolunlem2
    ralrimiva
    @8
    @10
    cxr
    wcel
    #
    @11
    cr
    wcel
    #
    @12
    @15
    wb
    @8
    @9
    cr
    wss
    #
    @17
    @0
    @4
    @19
    @2
    @6
    @0
    @4
    wa
    @19
    cA
    cB
    cr
    unss
    biimpi
    ad2ant2r
    @9
    ovolcl
    syl
    @2
    @6
    @18
    @0
    @4
    @1
    @5
    readdcl
    ad2ant2l
    vx
    @10
    @11
    xralrple
    syl2anc
    mpbird
end
