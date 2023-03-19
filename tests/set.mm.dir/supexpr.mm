include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cltp.mm"
include "wbr.mm"
include "wral.mm"
include "cnp.mm"
include "wrex.mm"
include "wa.mm"
include "cuni.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "suplem1pr.mm"
include "wss.mm"
include "ltrelpr.mm"
include "brel.mm"
include "simpld.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "rexlimivw.mm"
include "adantl.mm"
include "suplem2pr.mm"
include "ralrimiv.mm"
include "simprd.mm"
include "ralrimivw.mm"
include "jca.mm"
include "syl.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem supexpr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A =/= (/) /\ E. x e. P. A. y e. A y <P x ) -> E. x e. P. ( A. y e. A -. x <P y /\ A. y e. P. ( y <P x -> E. z e. A y <P z ) ) )

  proof
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cltp
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cnp
    wrex
    #
    wa
    #
    cA
    cuni
    #
    cnp
    wcel
    @7
    @1
    cltp
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @1
    @7
    cltp
    wbr
    #
    @1
    vz
    cv
    cltp
    wbr
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cnp
    wral
    #
    wa
    #
    @2
    @1
    cltp
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @3
    @12
    wi
    #
    vy
    cnp
    wral
    #
    wa
    #
    vx
    cnp
    wrex
    vx
    vy
    cA
    suplem1pr
    @6
    cA
    cnp
    wss
    #
    @15
    @5
    @22
    @0
    @4
    @22
    vx
    cnp
    @4
    @1
    cnp
    wcel
    #
    vy
    cA
    wral
    @22
    @3
    @23
    vy
    cA
    @3
    @23
    @2
    cnp
    wcel
    @1
    @2
    cnp
    cnp
    cltp
    ltrelpr
    brel
    simpld
    ralimi
    vy
    cA
    cnp
    dfss3
    sylibr
    rexlimivw
    adantl
    @22
    @10
    @14
    @22
    @9
    vy
    cA
    @22
    @1
    cA
    wcel
    @9
    wi
    #
    @13
    vy
    vz
    cA
    suplem2pr
    #
    simpld
    ralrimiv
    @22
    @13
    vy
    cnp
    @22
    @24
    @13
    @25
    simprd
    ralrimivw
    jca
    syl
    @21
    @15
    vx
    @7
    cnp
    @2
    @7
    wceq
    #
    @18
    @10
    @20
    @14
    @26
    @17
    @9
    vy
    cA
    @26
    @16
    @8
    @2
    @7
    @1
    cltp
    breq1
    notbid
    ralbidv
    @26
    @19
    @13
    vy
    cnp
    @26
    @3
    @11
    @12
    @2
    @7
    @1
    cltp
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    syl2anc
end
