include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "csconn.mm"
include "cconn.mm"
include "iccconn.mm"
include "wss.mm"
include "wb.mm"
include "iccssre.mm"
include "eqid.mm"
include "resconn.mm"
include "syl.mm"
include "mpbird.mm"

theorem iccsconn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( topGen ` ran (,) ) |`t ( A [,] B ) ) e. SConn )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cioo
    crn
    ctg
    cfv
    cA
    cB
    cicc
    co
    #
    crest
    co
    #
    csconn
    wcel
    #
    @2
    cconn
    wcel
    #
    cA
    cB
    iccconn
    @0
    @1
    cr
    wss
    @3
    @4
    wb
    cA
    cB
    iccssre
    @1
    @2
    @2
    eqid
    resconn
    syl
    mpbird
end
