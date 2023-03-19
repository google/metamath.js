include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "logltb.mm"
include "adantr.mm"
include "cr.mm"
include "cc0.mm"
include "relogcl.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "ad2antrl.mm"
include "log1.mm"
include "1rp.mm"
include "mpan.mm"
include "biimpa.mm"
include "syl5eqbrr.mm"
include "adantl.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "bitrd.mm"

theorem reglogltb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR+ /\ B e. RR+ ) /\ ( C e. RR+ /\ 1 < C ) ) -> ( A < B <-> ( ( log ` A ) / ( log ` C ) ) < ( ( log ` B ) / ( log ` C ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cC
    crp
    wcel
    #
    c1
    cC
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    clt
    wbr
    #
    @8
    cC
    clog
    cfv
    #
    cdiv
    co
    @9
    @11
    cdiv
    co
    clt
    wbr
    #
    @2
    @7
    @10
    wb
    @5
    cA
    cB
    logltb
    adantr
    @6
    @8
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    cc0
    @11
    clt
    wbr
    #
    @10
    @12
    wb
    @0
    @13
    @1
    @5
    cA
    relogcl
    ad2antrr
    @1
    @14
    @0
    @5
    cB
    relogcl
    ad2antlr
    @3
    @15
    @2
    @4
    cC
    relogcl
    ad2antrl
    @5
    @16
    @2
    @5
    cc0
    c1
    clog
    cfv
    #
    @11
    clt
    log1
    @3
    @4
    @17
    @11
    clt
    wbr
    #
    c1
    crp
    wcel
    @3
    @4
    @18
    wb
    1rp
    c1
    cC
    logltb
    mpan
    biimpa
    syl5eqbrr
    adantl
    @8
    @9
    @11
    ltdiv1
    syl112anc
    bitrd
end
