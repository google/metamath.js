include "cz.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "cneg.mm"
include "cn0.mm"
include "cn.mm"
include "wo.mm"
include "cr.mm"
include "wa.mm"
include "znegcl.mm"
include "elznn0nn.mm"
include "sylib.mm"
include "simpr.mm"
include "orim2i.mm"
include "syl.mm"
include "zcn.mm"
include "negnegd.mm"
include "eleq1d.mm"
include "orbi2d.mm"
include "mpbid.mm"
include "cc0.mm"
include "wceq.mm"
include "imbi2d.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "com12.mm"
include "a2d.mm"
include "nn0ind.mm"
include "nnnn0.mm"
include "syl11.mm"
include "mpdd.mm"
include "jaod.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "wb.mm"
include "negeq.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "bicomd.mm"
include "rspcdv.mm"
include "rspccv.mm"
include "3syl.mm"

theorem zindd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume zindd.1: |- ( x = 0 -> ( ph <-> ps ) )
  assume zindd.2: |- ( x = y -> ( ph <-> ch ) )
  assume zindd.3: |- ( x = ( y + 1 ) -> ( ph <-> ta ) )
  assume zindd.4: |- ( x = -u y -> ( ph <-> th ) )
  assume zindd.5: |- ( x = A -> ( ph <-> et ) )
  assume zindd.6: |- ( ze -> ps )
  assume zindd.7: |- ( ze -> ( y e. NN0 -> ( ch -> ta ) ) )
  assume zindd.8: |- ( ze -> ( y e. NN -> ( ch -> th ) ) )

  disjoint A x
  disjoint ch x
  disjoint et x
  disjoint ph y
  disjoint ps x
  disjoint ta x
  disjoint th x
  disjoint x y
  disjoint x ze
  disjoint y ze
  assert |- ( ze -> ( A e. ZZ -> et ) )

  proof
    wze
    wth
    vy
    cz
    wral
    #
    wph
    vx
    cz
    wral
    cA
    cz
    wcel
    wet
    wi
    wze
    wth
    vy
    cz
    vy
    cv
    #
    cz
    wcel
    #
    @1
    cneg
    #
    cn0
    wcel
    #
    @1
    cn
    wcel
    #
    wo
    #
    wze
    wth
    @2
    @4
    @3
    cneg
    #
    cn
    wcel
    #
    wo
    #
    @6
    @2
    @4
    @3
    cr
    wcel
    #
    @8
    wa
    #
    wo
    #
    @9
    @2
    @3
    cz
    wcel
    @12
    @1
    znegcl
    @3
    elznn0nn
    sylib
    @11
    @8
    @4
    @10
    @8
    simpr
    orim2i
    syl
    @2
    @8
    @5
    @4
    @2
    @7
    @1
    cn
    @2
    @1
    @1
    zcn
    negnegd
    eleq1d
    orbi2d
    mpbid
    wze
    @4
    wth
    @5
    @4
    wze
    wth
    wze
    wph
    wi
    #
    wze
    wps
    wi
    #
    wze
    wch
    wi
    #
    wze
    wta
    wi
    #
    wze
    wth
    wi
    vx
    vy
    @3
    vx
    cv
    #
    cc0
    wceq
    wph
    wps
    wze
    zindd.1
    imbi2d
    #
    @17
    @1
    wceq
    wph
    wch
    wze
    zindd.2
    imbi2d
    #
    @17
    @1
    c1
    caddc
    co
    wceq
    wph
    wta
    wze
    zindd.3
    imbi2d
    #
    @17
    @3
    wceq
    #
    wph
    wth
    wze
    zindd.4
    imbi2d
    zindd.6
    @1
    cn0
    wcel
    #
    wze
    wch
    wta
    wze
    @22
    wch
    wta
    wi
    zindd.7
    com12
    a2d
    #
    nn0ind
    com12
    wze
    @5
    wch
    wth
    @22
    wze
    wch
    @5
    @13
    @14
    @15
    @16
    @15
    vx
    vy
    @1
    @18
    @19
    @20
    @19
    zindd.6
    @23
    nn0ind
    @1
    nnnn0
    syl11
    zindd.8
    mpdd
    jaod
    syl5
    ralrimiv
    @0
    wph
    vx
    cz
    @17
    cz
    wcel
    #
    @0
    wph
    @24
    wth
    wph
    vy
    @17
    cneg
    #
    cz
    @17
    znegcl
    @24
    @1
    @25
    wceq
    #
    wa
    #
    wph
    wth
    @27
    @21
    wph
    wth
    wb
    @27
    @3
    @17
    @26
    @24
    @3
    @25
    cneg
    @17
    @1
    @25
    negeq
    @24
    @17
    @17
    zcn
    negnegd
    sylan9eqr
    eqcomd
    zindd.4
    syl
    bicomd
    rspcdv
    com12
    ralrimiv
    wph
    wet
    vx
    cA
    cz
    zindd.5
    rspccv
    3syl
end
