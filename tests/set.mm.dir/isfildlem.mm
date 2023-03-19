include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "wsbc.mm"
include "wa.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "ssexg.mm"
include "expcom.mm"
include "syl.mm"
include "adantrd.mm"
include "wb.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "sseq1.mm"
include "dfsbcq.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfan.mm"
include "nfbi.mm"
include "nfim.mm"
include "weq.mm"
include "sbceq1a.mm"
include "chvar.mm"
include "vtoclg.mm"
include "com12.mm"
include "pm5.21ndd.mm"

theorem isfildlem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume isfild.1: |- ( ph -> ( x e. F <-> ( x C_ A /\ ps ) ) )
  assume isfild.2: |- ( ph -> A e. _V )

  disjoint A x
  disjoint F x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint y z
  disjoint F z
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint B y
  assert |- ( ph -> ( B e. F <-> ( B C_ A /\ [. B / x ]. ps ) ) )

  proof
    wph
    cB
    cvv
    wcel
    #
    cB
    cF
    wcel
    #
    cB
    cA
    wss
    #
    wps
    vx
    cB
    wsbc
    #
    wa
    #
    @1
    @0
    wi
    wph
    cB
    cF
    elex
    a1i
    wph
    @2
    @0
    @3
    wph
    cA
    cvv
    wcel
    #
    @2
    @0
    wi
    isfild.2
    @2
    @5
    @0
    cB
    cA
    cvv
    ssexg
    expcom
    syl
    adantrd
    @0
    wph
    @1
    @4
    wb
    #
    wph
    vy
    cv
    #
    cF
    wcel
    #
    @7
    cA
    wss
    #
    wps
    vx
    @7
    wsbc
    #
    wa
    #
    wb
    #
    wi
    #
    wph
    @6
    wi
    vy
    cB
    cvv
    @7
    cB
    wceq
    #
    @12
    @6
    wph
    @14
    @8
    @1
    @11
    @4
    @7
    cB
    cF
    eleq1
    @14
    @9
    @2
    @10
    @3
    @7
    cB
    cA
    sseq1
    wps
    vx
    @7
    cB
    dfsbcq
    anbi12d
    bibi12d
    imbi2d
    wph
    vx
    cv
    #
    cF
    wcel
    #
    @15
    cA
    wss
    #
    wps
    wa
    #
    wb
    #
    wi
    @13
    vx
    vy
    wph
    @12
    vx
    wph
    vx
    nfv
    @8
    @11
    vx
    @8
    vx
    nfv
    @9
    @10
    vx
    @9
    vx
    nfv
    wps
    vx
    @7
    nfsbc1v
    nfan
    nfbi
    nfim
    vx
    vy
    weq
    #
    @19
    @12
    wph
    @20
    @16
    @8
    @18
    @11
    @15
    @7
    cF
    eleq1
    @20
    @17
    @9
    wps
    @10
    @15
    @7
    cA
    sseq1
    wps
    vx
    @7
    sbceq1a
    anbi12d
    bibi12d
    imbi2d
    isfild.1
    chvar
    vtoclg
    com12
    pm5.21ndd
end
