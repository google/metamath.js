include "cnq.mm"
include "wcel.mm"
include "wa.mm"
include "cltpq.mm"
include "wbr.mm"
include "cltq.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "clti.mm"
include "cxp.mm"
include "cin.mm"
include "brinxp.mm"
include "df-ltnq.mm"
include "breqi.mm"
include "syl6bbr.mm"
include "cop.mm"
include "cnpi.mm"
include "wrel.mm"
include "wceq.mm"
include "relxp.mm"
include "elpqn.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "breqan12d.mm"
include "ordpipq.mm"
include "syl6bb.mm"
include "bitr3d.mm"

theorem ordpinq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Q. /\ B e. Q. ) -> ( A <Q B <-> ( ( 1st ` A ) .N ( 2nd ` B ) ) <N ( ( 1st ` B ) .N ( 2nd ` A ) ) ) )

  proof
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    wa
    #
    cA
    cB
    cltpq
    wbr
    #
    cA
    cB
    cltq
    wbr
    #
    cA
    c1st
    cfv
    #
    cB
    c2nd
    cfv
    #
    cmi
    co
    cB
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cmi
    co
    clti
    wbr
    #
    @2
    @3
    cA
    cB
    cltpq
    cnq
    cnq
    cxp
    cin
    #
    wbr
    @4
    cA
    cB
    cnq
    cnq
    cltpq
    brinxp
    cA
    cB
    cltq
    @10
    df-ltnq
    breqi
    syl6bbr
    @2
    @3
    @5
    @8
    cop
    #
    @7
    @6
    cop
    #
    cltpq
    wbr
    @9
    @0
    @1
    cA
    @11
    cB
    @12
    cltpq
    @0
    cnpi
    cnpi
    cxp
    #
    wrel
    #
    cA
    @13
    wcel
    cA
    @11
    wceq
    cnpi
    cnpi
    relxp
    #
    cA
    elpqn
    cA
    @13
    1st2nd
    sylancr
    @1
    @14
    cB
    @13
    wcel
    cB
    @12
    wceq
    @15
    cB
    elpqn
    cB
    @13
    1st2nd
    sylancr
    breqan12d
    @5
    @8
    @7
    @6
    ordpipq
    syl6bb
    bitr3d
end
