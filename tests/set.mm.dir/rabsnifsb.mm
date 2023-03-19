include "cv.mm"
include "csn.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wsbc.mm"
include "c0.mm"
include "wn.mm"
include "wo.mm"
include "crab.mm"
include "cif.mm"
include "wceq.mm"
include "wi.mm"
include "elsni.mm"
include "sbceq1a.mm"
include "biimpd.mm"
include "syl.mm"
include "imdistani.mm"
include "orcd.mm"
include "biimprd.mm"
include "noel.mm"
include "pm2.21i.mm"
include "adantr.mm"
include "jaoi.mm"
include "impbii.mm"
include "abbii.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfan.mm"
include "nfn.mm"
include "nfor.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "orbi12d.mm"
include "cbvab.mm"
include "eqtri.mm"
include "df-rab.mm"
include "df-if.mm"
include "3eqtr4i.mm"

theorem rabsnifsb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- { x e. { A } | ph } = if ( [. A / x ]. ph , { A } , (/) )

  proof
    vx
    cv
    #
    cA
    csn
    #
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    vy
    cv
    #
    @1
    wcel
    #
    wph
    vx
    cA
    wsbc
    #
    wa
    #
    @5
    c0
    wcel
    #
    @7
    wn
    #
    wa
    #
    wo
    #
    vy
    cab
    #
    wph
    vx
    @1
    crab
    @7
    @1
    c0
    cif
    @4
    @2
    @7
    wa
    #
    @0
    c0
    wcel
    #
    @10
    wa
    #
    wo
    #
    vx
    cab
    @13
    @3
    @17
    vx
    @3
    @17
    @3
    @14
    @16
    @2
    wph
    @7
    @2
    @0
    cA
    wceq
    #
    wph
    @7
    wi
    @0
    cA
    elsni
    #
    @18
    wph
    @7
    wph
    vx
    cA
    sbceq1a
    #
    biimpd
    syl
    imdistani
    orcd
    @14
    @3
    @16
    @2
    @7
    wph
    @2
    @18
    @7
    wph
    wi
    @19
    @18
    wph
    @7
    @20
    biimprd
    syl
    imdistani
    @15
    @3
    @10
    @15
    @3
    @0
    noel
    pm2.21i
    adantr
    jaoi
    impbii
    abbii
    @17
    @12
    vx
    vy
    @17
    vy
    nfv
    @8
    @11
    vx
    @6
    @7
    vx
    @6
    vx
    nfv
    wph
    vx
    cA
    nfsbc1v
    #
    nfan
    @9
    @10
    vx
    @9
    vx
    nfv
    @7
    vx
    @21
    nfn
    nfan
    nfor
    vx
    vy
    weq
    #
    @14
    @8
    @16
    @11
    @22
    @2
    @6
    @7
    @0
    @5
    @1
    eleq1
    anbi1d
    @22
    @15
    @9
    @10
    @0
    @5
    c0
    eleq1
    anbi1d
    orbi12d
    cbvab
    eqtri
    wph
    vx
    @1
    df-rab
    @7
    vy
    @1
    c0
    df-if
    3eqtr4i
end
