include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cltp.mm"
include "wbr.mm"
include "cv.mm"
include "cpp.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "ltrelpr.mm"
include "brel.mm"
include "wpss.mm"
include "ltprord.mm"
include "wn.mm"
include "cplq.mm"
include "wex.mm"
include "cab.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "cbvabv.mm"
include "ltexprlem5.mm"
include "adantll.mm"
include "ltexprlem6.mm"
include "ltexprlem7.mm"
include "eqssd.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "sylbid.mm"
include "mpcom.mm"

theorem ltexpri
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( A <P B -> E. x e. P. ( A +P. x ) = B )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cA
    cB
    cltp
    wbr
    #
    cA
    vx
    cv
    #
    cpp
    co
    #
    cB
    wceq
    #
    vx
    cnp
    wrex
    #
    cA
    cB
    cnp
    cnp
    cltp
    ltrelpr
    brel
    @2
    @3
    cA
    cB
    wpss
    #
    @7
    cA
    cB
    ltprord
    @2
    @8
    @7
    @2
    @8
    wa
    #
    vw
    cv
    #
    cA
    wcel
    wn
    #
    @10
    vy
    cv
    #
    cplq
    co
    #
    cB
    wcel
    #
    wa
    #
    vw
    wex
    #
    vy
    cab
    #
    cnp
    wcel
    #
    cA
    @17
    cpp
    co
    #
    cB
    wceq
    #
    @7
    @1
    @8
    @18
    @0
    vz
    vw
    cA
    cB
    @17
    @16
    @11
    @10
    vz
    cv
    #
    cplq
    co
    #
    cB
    wcel
    #
    wa
    #
    vw
    wex
    vy
    vz
    @12
    @21
    wceq
    #
    @15
    @24
    vw
    @25
    @14
    @23
    @11
    @25
    @13
    @22
    cB
    @12
    @21
    @10
    cplq
    oveq2
    eleq1d
    anbi2d
    exbidv
    cbvabv
    #
    ltexprlem5
    adantll
    @9
    @19
    cB
    vz
    vw
    cA
    cB
    @17
    @26
    ltexprlem6
    vz
    vw
    cA
    cB
    @17
    @26
    ltexprlem7
    eqssd
    @6
    @20
    vx
    @17
    cnp
    @4
    @17
    wceq
    @5
    @19
    cB
    @4
    @17
    cA
    cpp
    oveq2
    eqeq1d
    rspcev
    syl2anc
    ex
    sylbid
    mpcom
end
