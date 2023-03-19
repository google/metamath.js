include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccld.mm"
include "cdif.mm"
include "cmnf.mm"
include "cpnf.mm"
include "cun.mm"
include "difreicc.mm"
include "ctop.mm"
include "retop.mm"
include "iooretop.mm"
include "unopn.mm"
include "mp3an.mm"
include "syl6eqel.mm"
include "wss.mm"
include "wb.mm"
include "iccssre.mm"
include "uniretop.mm"
include "iscld2.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem icccld
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A [,] B ) e. ( Clsd ` ( topGen ` ran (,) ) ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cA
    cB
    cicc
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    wcel
    #
    cr
    @1
    cdif
    #
    @2
    wcel
    #
    @0
    @4
    cmnf
    cA
    cioo
    co
    #
    cB
    cpnf
    cioo
    co
    #
    cun
    #
    @2
    cA
    cB
    difreicc
    @2
    ctop
    wcel
    #
    @6
    @2
    wcel
    @7
    @2
    wcel
    @8
    @2
    wcel
    retop
    cmnf
    cA
    iooretop
    cB
    cpnf
    iooretop
    @6
    @7
    @2
    unopn
    mp3an
    syl6eqel
    @0
    @9
    @1
    cr
    wss
    @3
    @5
    wb
    retop
    cA
    cB
    iccssre
    @1
    @2
    cr
    uniretop
    iscld2
    sylancr
    mpbird
end
