include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "eleq1.mm"
include "predeq3.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "predpredss.mm"
include "ad2antrr.mm"
include "wbr.mm"
include "weq.mm"
include "sseq1d.mm"
include "rspccva.mm"
include "sseld.mm"
include "vex.mm"
include "elpredim.mm"
include "a1i.mm"
include "jcad.mm"
include "wb.mm"
include "elpred.mm"
include "adantl.mm"
include "mpbird.mm"
include "ssrdv.mm"
include "adantll.mm"
include "eqssd.mm"
include "ex.mm"
include "vtoclg.mm"
include "pm2.43b.mm"

theorem preddowncl
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint X y
  assert |- ( ( B C_ A /\ A. x e. B Pred ( R , A , x ) C_ B ) -> ( X e. B -> Pred ( R , B , X ) = Pred ( R , A , X ) ) )

  proof
    cB
    cA
    wss
    #
    cA
    cR
    vx
    cv
    #
    cpred
    #
    cB
    wss
    #
    vx
    cB
    wral
    #
    wa
    #
    cX
    cB
    wcel
    #
    cB
    cR
    cX
    cpred
    #
    cA
    cR
    cX
    cpred
    #
    wceq
    #
    @5
    vy
    cv
    #
    cB
    wcel
    #
    cB
    cR
    @10
    cpred
    #
    cA
    cR
    @10
    cpred
    #
    wceq
    #
    wi
    #
    wi
    @5
    @6
    @9
    wi
    #
    wi
    vy
    cX
    cB
    @10
    cX
    wceq
    #
    @15
    @16
    @5
    @17
    @11
    @6
    @14
    @9
    @10
    cX
    cB
    eleq1
    @17
    @12
    @7
    @13
    @8
    cB
    cR
    @10
    cX
    predeq3
    cA
    cR
    @10
    cX
    predeq3
    eqeq12d
    imbi12d
    imbi2d
    @5
    @11
    @14
    @5
    @11
    wa
    @12
    @13
    @0
    @12
    @13
    wss
    @4
    @11
    cB
    cA
    cR
    @10
    predpredss
    ad2antrr
    @4
    @11
    @13
    @12
    wss
    @0
    @4
    @11
    wa
    #
    vz
    @13
    @12
    @18
    vz
    cv
    #
    @13
    wcel
    #
    @19
    @12
    wcel
    #
    wi
    #
    @20
    @19
    cB
    wcel
    #
    @19
    @10
    cR
    wbr
    #
    wa
    #
    wi
    #
    @18
    @20
    @23
    @24
    @18
    @13
    cB
    @19
    @3
    @13
    cB
    wss
    vx
    @10
    cB
    vx
    vy
    weq
    @2
    @13
    cB
    cA
    cR
    @1
    @10
    predeq3
    sseq1d
    rspccva
    sseld
    @20
    @24
    wi
    @18
    cA
    cR
    @10
    @19
    vy
    vex
    elpredim
    a1i
    jcad
    @11
    @22
    @26
    wb
    @4
    @11
    @21
    @25
    @20
    cB
    cB
    cR
    @10
    @19
    vz
    vex
    elpred
    imbi2d
    adantl
    mpbird
    ssrdv
    adantll
    eqssd
    ex
    vtoclg
    pm2.43b
end
