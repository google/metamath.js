include "cfn.mm"
include "wcel.mm"
include "cr.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wss.mm"
include "r19.29.mm"
include "eleq1.mm"
include "biimparc.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "abssdv.mm"
include "abrexfi.mm"
include "fimaxre2.mm"
include "syl2anr.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "r19.23v.mm"
include "albii.mm"
include "ralcom4.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "ralab.mm"
include "3bitr4i.mm"
include "nfv.mm"
include "breq1.mm"
include "ceqsalg.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl5bbr.mm"
include "adantl.mm"
include "mpbid.mm"

theorem fimaxre3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  assert |- ( ( A e. Fin /\ A. y e. A B e. RR ) -> E. x e. RR A. y e. A B <_ x )

  proof
    cA
    cfn
    wcel
    #
    cB
    cr
    wcel
    #
    vy
    cA
    wral
    #
    wa
    vw
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vw
    vz
    cv
    #
    cB
    wceq
    #
    vy
    cA
    wrex
    #
    vz
    cab
    #
    wral
    #
    vx
    cr
    wrex
    #
    cB
    @4
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @2
    @9
    cr
    wss
    @9
    cfn
    wcel
    @11
    @0
    @2
    @8
    vz
    cr
    @2
    @8
    @6
    cr
    wcel
    #
    @2
    @8
    wa
    @1
    @7
    wa
    #
    vy
    cA
    wrex
    @15
    @1
    @7
    vy
    cA
    r19.29
    @16
    @15
    vy
    cA
    @7
    @15
    @1
    @6
    cB
    cr
    eleq1
    biimparc
    rexlimivw
    syl
    ex
    abssdv
    vy
    vz
    cA
    cB
    abrexfi
    vx
    vw
    @9
    fimaxre2
    syl2anr
    @2
    @11
    @14
    wb
    @0
    @2
    @10
    @13
    vx
    cr
    @10
    @3
    cB
    wceq
    #
    @5
    wi
    #
    vw
    wal
    #
    vy
    cA
    wral
    #
    @2
    @13
    @18
    vy
    cA
    wral
    #
    vw
    wal
    @17
    vy
    cA
    wrex
    #
    @5
    wi
    #
    vw
    wal
    @20
    @10
    @21
    @23
    vw
    @17
    @5
    vy
    cA
    r19.23v
    albii
    @18
    vy
    vw
    cA
    ralcom4
    @8
    @22
    @5
    vw
    vz
    @6
    @3
    wceq
    @7
    @17
    vy
    cA
    @6
    @3
    cB
    eqeq1
    rexbidv
    ralab
    3bitr4i
    @2
    @19
    @12
    wb
    #
    vy
    cA
    wral
    @20
    @13
    wb
    @1
    @24
    vy
    cA
    @5
    @12
    vw
    cB
    cr
    @12
    vw
    nfv
    @3
    cB
    @4
    cle
    breq1
    ceqsalg
    ralimi
    @19
    @12
    vy
    cA
    ralbi
    syl
    syl5bbr
    rexbidv
    adantl
    mpbid
end
