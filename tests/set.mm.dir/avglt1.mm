include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cdiv.mm"
include "wb.mm"
include "ltadd2.mm"
include "3anidm13.mm"
include "cc.mm"
include "wceq.mm"
include "simpl.mm"
include "recnd.mm"
include "times2.mm"
include "syl.mm"
include "breq1d.mm"
include "cc0.mm"
include "readdcl.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "ltmuldiv.mm"
include "syl3anc.mm"
include "3bitr2d.mm"

theorem avglt1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> A < ( ( A + B ) / 2 ) ) )

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
    clt
    wbr
    #
    cA
    cA
    caddc
    co
    #
    cA
    cB
    caddc
    co
    #
    clt
    wbr
    #
    cA
    c2
    cmul
    co
    #
    @5
    clt
    wbr
    #
    cA
    @5
    c2
    cdiv
    co
    clt
    wbr
    #
    @0
    @1
    @3
    @6
    wb
    cA
    cB
    cA
    ltadd2
    3anidm13
    @2
    @7
    @4
    @5
    clt
    @2
    cA
    cc
    wcel
    @7
    @4
    wceq
    @2
    cA
    @0
    @1
    simpl
    #
    recnd
    cA
    times2
    syl
    breq1d
    @2
    @0
    @5
    cr
    wcel
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
    @9
    wb
    @10
    cA
    cB
    readdcl
    @13
    @2
    @11
    @12
    2re
    2pos
    pm3.2i
    a1i
    cA
    @5
    c2
    ltmuldiv
    syl3anc
    3bitr2d
end
