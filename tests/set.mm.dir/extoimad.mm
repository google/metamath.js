include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cr.mm"
include "cima.mm"
include "wral.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "abscld.mm"
include "ccom.mm"
include "wceq.mm"
include "wrex.mm"
include "imaco.mm"
include "a1i.mm"
include "eleq2d.mm"
include "wf.mm"
include "wfn.mm"
include "cc.mm"
include "absf.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fssresd.mm"
include "fco2d.mm"
include "wi.mm"
include "ffn.mm"
include "mpd.mm"
include "ssid.mm"
include "fvelimabd.mm"
include "wb.mm"
include "eqcom.mm"
include "rexbidv.mm"
include "bitrd.mm"
include "adantr.mm"
include "simpr.mm"
include "fvco3d.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "bitr4d.mm"
include "bitr3d.mm"
include "breq1d.mm"
include "ralxfr2d.mm"
include "mpbird.mm"

theorem extoimad
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  assume extoimad.1: |- ( ph -> F : RR --> RR )
  assume extoimad.2: |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ C )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A. x e. ( abs " ( F " RR ) ) x <_ C )

  proof
    wph
    vx
    cv
    #
    cC
    cle
    wbr
    #
    vx
    cabs
    cF
    cr
    cima
    cima
    #
    wral
    vy
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cC
    cle
    wbr
    #
    vy
    cr
    wral
    extoimad.2
    wph
    @1
    @6
    vx
    vy
    @5
    @2
    cr
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @4
    @8
    @4
    wph
    cr
    cr
    @3
    cF
    extoimad.1
    ffvelrnda
    recnd
    abscld
    wph
    @0
    cabs
    cF
    ccom
    #
    cr
    cima
    #
    wcel
    #
    @0
    @2
    wcel
    @0
    @5
    wceq
    #
    vy
    cr
    wrex
    #
    wph
    @10
    @2
    @0
    @10
    @2
    wceq
    wph
    cabs
    cF
    cr
    imaco
    a1i
    eleq2d
    wph
    @11
    @0
    @3
    @9
    cfv
    #
    wceq
    #
    vy
    cr
    wrex
    #
    @13
    wph
    @11
    @14
    @0
    wceq
    #
    vy
    cr
    wrex
    @16
    wph
    vy
    cr
    cr
    @0
    @9
    wph
    cr
    cr
    @9
    wf
    #
    @9
    cr
    wfn
    #
    wph
    cr
    cr
    cr
    cabs
    cF
    extoimad.1
    wph
    cc
    cr
    cr
    cabs
    cc
    cr
    cabs
    wf
    wph
    absf
    a1i
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssresd
    fco2d
    @18
    @19
    wi
    wph
    cr
    cr
    @9
    ffn
    a1i
    mpd
    cr
    cr
    wss
    wph
    cr
    ssid
    a1i
    fvelimabd
    wph
    @17
    @15
    vy
    cr
    @17
    @15
    wb
    wph
    @14
    @0
    eqcom
    a1i
    rexbidv
    bitrd
    wph
    @12
    @15
    vy
    cr
    @8
    @5
    @14
    @0
    @8
    @14
    @5
    @8
    cr
    cr
    @3
    cabs
    cF
    wph
    cr
    cr
    cF
    wf
    @7
    extoimad.1
    adantr
    wph
    @7
    simpr
    fvco3d
    eqcomd
    eqeq2d
    rexbidva
    bitr4d
    bitr3d
    wph
    @12
    wa
    @0
    @5
    cC
    cle
    wph
    @12
    simpr
    breq1d
    ralxfr2d
    mpbird
end
