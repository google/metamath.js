include "cn0.mm"
include "wcel.mm"
include "wsbc.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wa.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "cv.mm"
include "wceq.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "dfsbcq.mm"
include "anbi12d.mm"
include "weq.mm"
include "ovex.mm"
include "cc0.mm"
include "wb.mm"
include "1m1e0.mm"
include "eqeq2i.mm"
include "sylbi.mm"
include "sbcie.mm"
include "mpbir.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "simprr.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "adantr.mm"
include "mpbird.mm"
include "vex.mm"
include "anbi12i.mm"
include "3imtr4g.mm"
include "imp.mm"
include "jca.mm"
include "ex.mm"
include "nnind.mm"
include "syl.mm"
include "nn0cn.mm"
include "biimpa.mm"
include "adantrr.mm"
include "mpdan.mm"
include "sbcieg.mm"
include "mpbid.mm"

theorem 2nn0ind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let va: setvar a
  assume 2nn0ind.1: |- ps
  assume 2nn0ind.2: |- ch
  assume 2nn0ind.3: |- ( y e. NN -> ( ( th /\ ta ) -> et ) )
  assume 2nn0ind.4: |- ( x = 0 -> ( ph <-> ps ) )
  assume 2nn0ind.5: |- ( x = 1 -> ( ph <-> ch ) )
  assume 2nn0ind.6: |- ( x = ( y - 1 ) -> ( ph <-> th ) )
  assume 2nn0ind.7: |- ( x = y -> ( ph <-> ta ) )
  assume 2nn0ind.8: |- ( x = ( y + 1 ) -> ( ph <-> et ) )
  assume 2nn0ind.9: |- ( x = A -> ( ph <-> rh ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint et x
  disjoint rh x
  disjoint ph y
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint a ps
  disjoint a ch
  disjoint a th
  disjoint a ta
  disjoint a et
  disjoint a rh
  disjoint a ph
  assert |- ( A e. NN0 -> rh )

  proof
    cA
    cn0
    wcel
    #
    wph
    vx
    cA
    wsbc
    #
    wrh
    @0
    wph
    vx
    cA
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    wsbc
    #
    wph
    vx
    @2
    wsbc
    #
    wa
    #
    @1
    @0
    @2
    cn
    wcel
    @6
    cA
    nn0p1nn
    wph
    vx
    va
    cv
    #
    c1
    cmin
    co
    #
    wsbc
    #
    wph
    vx
    @7
    wsbc
    #
    wa
    wph
    vx
    c1
    c1
    cmin
    co
    #
    wsbc
    #
    wph
    vx
    c1
    wsbc
    #
    wa
    wph
    vx
    vy
    cv
    #
    c1
    cmin
    co
    #
    wsbc
    #
    wph
    vx
    @14
    wsbc
    #
    wa
    #
    wph
    vx
    @14
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    wsbc
    #
    wph
    vx
    @19
    wsbc
    #
    wa
    #
    @6
    va
    vy
    @2
    @7
    c1
    wceq
    #
    @9
    @12
    @10
    @13
    @24
    wph
    vx
    @8
    @11
    @7
    c1
    c1
    cmin
    oveq1
    sbceq1d
    wph
    vx
    @7
    c1
    dfsbcq
    anbi12d
    va
    vy
    weq
    #
    @9
    @16
    @10
    @17
    @25
    wph
    vx
    @8
    @15
    @7
    @14
    c1
    cmin
    oveq1
    sbceq1d
    wph
    vx
    @7
    @14
    dfsbcq
    anbi12d
    @7
    @19
    wceq
    #
    @9
    @21
    @10
    @22
    @26
    wph
    vx
    @8
    @20
    @7
    @19
    c1
    cmin
    oveq1
    sbceq1d
    wph
    vx
    @7
    @19
    dfsbcq
    anbi12d
    @7
    @2
    wceq
    #
    @9
    @4
    @10
    @5
    @27
    wph
    vx
    @8
    @3
    @7
    @2
    c1
    cmin
    oveq1
    sbceq1d
    wph
    vx
    @7
    @2
    dfsbcq
    anbi12d
    @12
    @13
    @12
    wps
    2nn0ind.1
    wph
    wps
    vx
    @11
    c1
    c1
    cmin
    ovex
    vx
    cv
    #
    @11
    wceq
    @28
    cc0
    wceq
    wph
    wps
    wb
    @11
    cc0
    @28
    1m1e0
    eqeq2i
    2nn0ind.4
    sylbi
    sbcie
    mpbir
    @13
    wch
    2nn0ind.2
    wph
    wch
    vx
    c1
    1ex
    2nn0ind.5
    sbcie
    mpbir
    pm3.2i
    @14
    cn
    wcel
    #
    @18
    @23
    @29
    @18
    wa
    #
    @21
    @22
    @30
    @21
    @17
    @29
    @16
    @17
    simprr
    @30
    wph
    vx
    @20
    @14
    @29
    @20
    @14
    wceq
    #
    @18
    @29
    @14
    cc
    wcel
    c1
    cc
    wcel
    #
    @31
    @14
    nncn
    ax-1cn
    @14
    c1
    pncan
    sylancl
    adantr
    sbceq1d
    mpbird
    @29
    @18
    @22
    @29
    wth
    wta
    wa
    wet
    @18
    @22
    2nn0ind.3
    @16
    wth
    @17
    wta
    wph
    wth
    vx
    @15
    @14
    c1
    cmin
    ovex
    2nn0ind.6
    sbcie
    wph
    wta
    vx
    @14
    vy
    vex
    2nn0ind.7
    sbcie
    anbi12i
    wph
    wet
    vx
    @19
    @14
    c1
    caddc
    ovex
    2nn0ind.8
    sbcie
    3imtr4g
    imp
    jca
    ex
    nnind
    syl
    @0
    @4
    @1
    @5
    @0
    @4
    @1
    @0
    wph
    vx
    @3
    cA
    @0
    cA
    cc
    wcel
    @32
    @3
    cA
    wceq
    cA
    nn0cn
    ax-1cn
    cA
    c1
    pncan
    sylancl
    sbceq1d
    biimpa
    adantrr
    mpdan
    wph
    wrh
    vx
    cA
    cn0
    2nn0ind.9
    sbcieg
    mpbid
end
