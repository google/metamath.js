include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "clog.mm"
include "cfv.mm"
include "cle.mm"
include "wb.mm"
include "logltb.mm"
include "ancoms.mm"
include "notbid.mm"
include "cr.mm"
include "rpre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "relogcl.mm"
include "3bitr4d.mm"

theorem logleb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A <_ B <-> ( log ` A ) <_ ( log ` B ) ) )

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
    cB
    cA
    clt
    wbr
    #
    wn
    #
    cB
    clog
    cfv
    #
    cA
    clog
    cfv
    #
    clt
    wbr
    #
    wn
    #
    cA
    cB
    cle
    wbr
    #
    @6
    @5
    cle
    wbr
    #
    @2
    @3
    @7
    @1
    @0
    @3
    @7
    wb
    cB
    cA
    logltb
    ancoms
    notbid
    @0
    cA
    cr
    wcel
    cB
    cr
    wcel
    @9
    @4
    wb
    @1
    cA
    rpre
    cB
    rpre
    cA
    cB
    lenlt
    syl2an
    @0
    @6
    cr
    wcel
    @5
    cr
    wcel
    @10
    @8
    wb
    @1
    cA
    relogcl
    cB
    relogcl
    @6
    @5
    lenlt
    syl2an
    3bitr4d
end
