include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "wceq.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "cc.mm"
include "wb.mm"
include "recn.mm"
include "efival.mm"
include "eqeqan12d.mm"
include "syl2an.mm"
include "recoscl.mm"
include "resincl.mm"
include "jca.mm"
include "cru.mm"
include "bitrd.mm"

theorem efieq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( exp ` ( _i x. A ) ) = ( exp ` ( _i x. B ) ) <-> ( ( cos ` A ) = ( cos ` B ) /\ ( sin ` A ) = ( sin ` B ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    ci
    cA
    cmul
    co
    ce
    cfv
    #
    ci
    cB
    cmul
    co
    ce
    cfv
    #
    wceq
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
    caddc
    co
    #
    cB
    ccos
    cfv
    #
    ci
    cB
    csin
    cfv
    #
    cmul
    co
    caddc
    co
    #
    wceq
    #
    @5
    @8
    wceq
    @6
    @9
    wceq
    wa
    #
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @4
    @11
    wb
    @1
    cA
    recn
    cB
    recn
    @13
    @14
    @2
    @7
    @3
    @10
    cA
    efival
    cB
    efival
    eqeqan12d
    syl2an
    @0
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    @8
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    wa
    @11
    @12
    wb
    @1
    @0
    @15
    @16
    cA
    recoscl
    cA
    resincl
    jca
    @1
    @17
    @18
    cB
    recoscl
    cB
    resincl
    jca
    @5
    @6
    @8
    @9
    cru
    syl2an
    bitrd
end
