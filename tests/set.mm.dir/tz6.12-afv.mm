include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "weu.mm"
include "wa.mm"
include "cafv.mm"
include "wceq.mm"
include "wi.mm"
include "cfv.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wbr.mm"
include "simpl.mm"
include "vex.mm"
include "a1i.mm"
include "df-br.mm"
include "biimpri.mm"
include "adantl.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "wral.mm"
include "velsn.mm"
include "wb.mm"
include "breq1.mm"
include "syl5bbr.mm"
include "eqcoms.mm"
include "eubidv.mm"
include "biimpd.mm"
include "sylbi.mm"
include "com12.mm"
include "ralrimiv.mm"
include "wfn.mm"
include "fnres.mm"
include "fnfun.mm"
include "sylbir.mm"
include "syl.mm"
include "jca.mm"
include "ex.mm"
include "impr.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "afvfundmfveq.mm"
include "tz6.12.mm"
include "eqtrd.mm"
include "wn.mm"
include "eu2ndop1stv.mm"
include "pm2.24d.mm"
include "pm2.61i.mm"

theorem tz6.12-afv
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vk: setvar k

  disjoint A y
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint F x
  disjoint k x
  assert |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F ) -> ( F ''' A ) = y )

  proof
    cA
    cvv
    wcel
    #
    cA
    vy
    cv
    #
    cop
    cF
    wcel
    #
    @2
    vy
    weu
    #
    wa
    #
    cA
    cF
    cafv
    #
    @1
    wceq
    #
    wi
    @0
    @4
    @6
    @0
    @4
    wa
    #
    @5
    cA
    cF
    cfv
    #
    @1
    @7
    cA
    cF
    cdm
    wcel
    #
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    wa
    #
    @5
    @8
    wceq
    #
    @0
    @2
    @3
    @13
    @0
    @2
    wa
    #
    @9
    @3
    @13
    wi
    @15
    @0
    @1
    cvv
    wcel
    #
    cA
    @1
    cF
    wbr
    #
    @9
    @0
    @2
    simpl
    @16
    @15
    vy
    vex
    a1i
    @2
    @17
    @0
    @17
    @2
    cA
    @1
    cF
    df-br
    #
    biimpri
    adantl
    cA
    @1
    cvv
    cvv
    cF
    breldmg
    syl3anc
    @9
    @3
    @13
    @9
    @3
    wa
    #
    @9
    @12
    @9
    @3
    simpl
    @19
    vx
    cv
    #
    @1
    cF
    wbr
    #
    vy
    weu
    #
    vx
    @10
    wral
    #
    @12
    @19
    @22
    vx
    @10
    @3
    @20
    @10
    wcel
    #
    @22
    wi
    @9
    @24
    @3
    @22
    @24
    @20
    cA
    wceq
    #
    @3
    @22
    wi
    vx
    cA
    velsn
    @25
    @3
    @22
    @25
    @2
    @21
    vy
    @2
    @21
    wb
    cA
    @20
    @2
    @17
    cA
    @20
    wceq
    @21
    @18
    cA
    @20
    @1
    cF
    breq1
    syl5bbr
    eqcoms
    eubidv
    biimpd
    sylbi
    com12
    adantl
    ralrimiv
    @23
    @11
    @10
    wfn
    @12
    vx
    vy
    @10
    cF
    fnres
    @10
    @11
    fnfun
    sylbir
    syl
    jca
    ex
    syl
    impr
    @13
    cA
    cF
    wdfat
    @14
    cA
    cF
    df-dfat
    cA
    cF
    afvfundmfveq
    sylbir
    syl
    @4
    @8
    @1
    wceq
    @0
    vy
    cA
    cF
    tz6.12
    adantl
    eqtrd
    ex
    @4
    @0
    wn
    #
    @6
    @3
    @26
    @6
    wi
    @2
    @3
    @0
    @6
    vy
    cA
    cF
    eu2ndop1stv
    pm2.24d
    adantl
    com12
    pm2.61i
end
