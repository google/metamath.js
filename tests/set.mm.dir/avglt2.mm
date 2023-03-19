include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "cc.mm"
include "wceq.mm"
include "simpr.mm"
include "recnd.mm"
include "2times.mm"
include "syl.mm"
include "breq2d.mm"
include "cc0.mm"
include "wb.mm"
include "readdcl.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "ltdivmul.mm"
include "syl3anc.mm"
include "ltadd1.mm"
include "3anidm23.mm"
include "3bitr4rd.mm"

theorem avglt2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> ( ( A + B ) / 2 ) < B ) )

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
    #
    cA
    cB
    caddc
    co
    #
    c2
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @3
    cB
    cB
    caddc
    co
    #
    clt
    wbr
    #
    @3
    c2
    cdiv
    co
    cB
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    @2
    @4
    @6
    @3
    clt
    @2
    cB
    cc
    wcel
    @4
    @6
    wceq
    @2
    cB
    @0
    @1
    simpr
    #
    recnd
    cB
    2times
    syl
    breq2d
    @2
    @3
    cr
    wcel
    @1
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @8
    @5
    wb
    cA
    cB
    readdcl
    @10
    @13
    @2
    @11
    @12
    2re
    2pos
    pm3.2i
    a1i
    @3
    cB
    c2
    ltdivmul
    syl3anc
    @0
    @1
    @9
    @7
    wb
    cA
    cB
    cB
    ltadd1
    3anidm23
    3bitr4rd
end
