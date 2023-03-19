include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "clt.mm"
include "cinf.mm"
include "simpr.mm"
include "wrex.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "3ad2antl3.mm"
include "simpl3.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"

theorem infmrgelbi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x z
  disjoint A z
  disjoint B z
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ B e. RR ) /\ A. x e. A B <_ x ) -> B <_ inf ( A , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    cB
    cr
    wcel
    #
    w3a
    #
    cB
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    wa
    #
    cB
    cA
    cr
    clt
    cinf
    cle
    wbr
    #
    @6
    @3
    @6
    simpr
    @7
    @0
    @1
    vz
    cv
    #
    @4
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    @2
    @8
    @6
    wb
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl2
    @2
    @0
    @6
    @12
    @1
    @11
    @6
    vz
    cB
    cr
    @9
    cB
    wceq
    @10
    @5
    vx
    cA
    @9
    cB
    @4
    cle
    breq1
    ralbidv
    rspcev
    3ad2antl3
    @0
    @1
    @2
    @6
    simpl3
    vz
    vx
    vx
    cA
    cB
    infregelb
    syl31anc
    mpbird
end
