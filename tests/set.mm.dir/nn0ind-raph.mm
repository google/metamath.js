include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "elnn0.mm"
include "wsb.mm"
include "c1.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "nfv.mm"
include "sbhypf.mm"
include "caddc.mm"
include "co.mm"
include "nfsbc1v.mm"
include "1ex.mm"
include "wi.mm"
include "c0ex.mm"
include "wa.mm"
include "0nn0.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "mpbiri.mm"
include "wb.mm"
include "eqeq2.mm"
include "syl6bir.mm"
include "pm5.74d.mm"
include "mpbii.mm"
include "com12.mm"
include "vtocle.mm"
include "sylc.mm"
include "adantr.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "imp.mm"
include "mpbird.mm"
include "ex.mm"
include "sbceq1a.mm"
include "mpbid.mm"
include "vtoclef.mm"
include "nnnn0.mm"
include "syl.mm"
include "nnind.mm"
include "eqeq1.mm"
include "bicomd.mm"
include "sylan9bb.mm"
include "sylbird.mm"
include "eqcoms.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem nn0ind-raph
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume nn0ind-raph.1: |- ( x = 0 -> ( ph <-> ps ) )
  assume nn0ind-raph.2: |- ( x = y -> ( ph <-> ch ) )
  assume nn0ind-raph.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume nn0ind-raph.4: |- ( x = A -> ( ph <-> ta ) )
  assume nn0ind-raph.5: |- ps
  assume nn0ind-raph.6: |- ( y e. NN0 -> ( ch -> th ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ps z
  disjoint ch z
  disjoint th z
  disjoint ta z
  disjoint ph z
  assert |- ( A e. NN0 -> ta )

  proof
    cA
    cn0
    wcel
    cA
    cn
    wcel
    #
    cA
    cc0
    wceq
    #
    wo
    wta
    cA
    elnn0
    @0
    wta
    @1
    wph
    vx
    vz
    wsb
    wph
    vx
    c1
    wsbc
    #
    wch
    wth
    wta
    vz
    vy
    cA
    wph
    vx
    vz
    c1
    dfsbcq2
    wph
    wch
    vx
    vz
    vy
    cv
    #
    wch
    vx
    nfv
    nn0ind-raph.2
    sbhypf
    wph
    wth
    vx
    vz
    @3
    c1
    caddc
    co
    #
    wth
    vx
    nfv
    nn0ind-raph.3
    sbhypf
    wph
    wta
    vx
    vz
    cA
    wta
    vx
    nfv
    nn0ind-raph.4
    sbhypf
    @2
    vx
    c1
    wph
    vx
    c1
    nfsbc1v
    1ex
    vx
    cv
    #
    c1
    wceq
    #
    wph
    @2
    @6
    wph
    wi
    vy
    cc0
    c0ex
    @3
    cc0
    wceq
    #
    @6
    wph
    @7
    @6
    wa
    wph
    wth
    @7
    wth
    @6
    @7
    @3
    cn0
    wcel
    #
    wch
    wth
    cc0
    cn0
    wcel
    @7
    @8
    wi
    0nn0
    cc0
    cn0
    @3
    eleq1a
    ax-mp
    @7
    wch
    wi
    vx
    cc0
    c0ex
    @7
    @5
    cc0
    wceq
    #
    wch
    @7
    @9
    wph
    wi
    @9
    wch
    wi
    @9
    wph
    wps
    nn0ind-raph.5
    nn0ind-raph.1
    mpbiri
    @7
    @9
    wph
    wch
    @7
    @9
    @5
    @3
    wceq
    wph
    wch
    wb
    @3
    cc0
    @5
    eqeq2
    nn0ind-raph.2
    syl6bir
    pm5.74d
    mpbii
    com12
    vtocle
    nn0ind-raph.6
    sylc
    adantr
    @7
    @6
    wph
    wth
    wb
    #
    @7
    @6
    @5
    @4
    wceq
    @10
    @7
    @4
    c1
    @5
    @7
    @4
    cc0
    c1
    caddc
    co
    c1
    @3
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    eqeq2d
    nn0ind-raph.3
    syl6bir
    imp
    mpbird
    ex
    vtocle
    wph
    vx
    c1
    sbceq1a
    mpbid
    vtoclef
    @3
    cn
    wcel
    @8
    wch
    wth
    wi
    @3
    nnnn0
    nn0ind-raph.6
    syl
    nnind
    wta
    cc0
    cA
    cc0
    cA
    wceq
    #
    wta
    wi
    #
    vx
    cc0
    @12
    vx
    nfv
    c0ex
    @9
    @11
    @5
    cA
    wceq
    #
    wta
    @5
    cc0
    cA
    eqeq1
    @9
    @13
    wta
    @9
    @13
    wa
    wps
    wta
    nn0ind-raph.5
    @9
    wps
    wph
    @13
    wta
    @9
    wph
    wps
    nn0ind-raph.1
    bicomd
    nn0ind-raph.4
    sylan9bb
    mpbii
    ex
    sylbird
    vtoclef
    eqcoms
    jaoi
    sylbi
end
