include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "ceq.mm"
include "wbr.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cmi.mm"
include "co.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "breqan12d.mm"
include "wb.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "jca.mm"
include "enqbreq.mm"
include "syl2an.mm"
include "mulcompi.mm"
include "eqeq2i.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem enqbreq2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( N. X. N. ) /\ B e. ( N. X. N. ) ) -> ( A ~Q B <-> ( ( 1st ` A ) .N ( 2nd ` B ) ) = ( ( 1st ` B ) .N ( 2nd ` A ) ) ) )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    ceq
    wbr
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cop
    #
    cB
    c1st
    cfv
    #
    cB
    c2nd
    cfv
    #
    cop
    #
    ceq
    wbr
    #
    @4
    @8
    cmi
    co
    #
    @5
    @7
    cmi
    co
    #
    wceq
    #
    @11
    @7
    @5
    cmi
    co
    #
    wceq
    #
    @1
    @2
    cA
    @6
    cB
    @9
    ceq
    cA
    cnpi
    cnpi
    1st2nd2
    cB
    cnpi
    cnpi
    1st2nd2
    breqan12d
    @1
    @4
    cnpi
    wcel
    #
    @5
    cnpi
    wcel
    #
    wa
    @7
    cnpi
    wcel
    #
    @8
    cnpi
    wcel
    #
    wa
    @10
    @13
    wb
    @2
    @1
    @16
    @17
    cA
    cnpi
    cnpi
    xp1st
    cA
    cnpi
    cnpi
    xp2nd
    jca
    @2
    @18
    @19
    cB
    cnpi
    cnpi
    xp1st
    cB
    cnpi
    cnpi
    xp2nd
    jca
    @4
    @5
    @7
    @8
    enqbreq
    syl2an
    @13
    @15
    wb
    @3
    @12
    @14
    @11
    @5
    @7
    mulcompi
    eqeq2i
    a1i
    3bitrd
end
