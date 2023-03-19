include "cabs.mm"
include "cr.mm"
include "cima.mm"
include "cc0.mm"
include "ccom.mm"
include "imaco.mm"
include "eqcomi.mm"
include "crn.mm"
include "wss.mm"
include "imassrn.mm"
include "a1i.mm"
include "wf.mm"
include "cc.mm"
include "absf.mm"
include "ax-resscn.mm"
include "fssresd.mm"
include "fco2d.mm"
include "frn.mm"
include "syl.mm"
include "sstrd.mm"
include "syl5eqss.mm"
include "c0.mm"
include "wne.mm"
include "0re.mm"
include "ne0ii.mm"
include "wnefimgd.mm"
include "necomd.mm"
include "wceq.mm"
include "neeqtrrd.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "c1.mm"
include "1red.mm"
include "wa.mm"
include "simpr.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "extoimad.mm"
include "rspcedvd.mm"
include "0red.mm"
include "cfv.mm"
include "clt.mm"
include "wrex.mm"
include "wcel.mm"
include "adantr.mm"
include "simprl.mm"
include "fvco3d.mm"
include "funfvima2d.mm"
include "adantrr.mm"
include "syl6eleq.mm"
include "eqeltrrd.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "simprr.mm"
include "absrpcld.mm"
include "rpgt0d.mm"
include "rexlimddv.mm"
include "suprlubrd.mm"

theorem imo72b2lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vc: setvar c
  let vt: setvar t
  let vz: setvar z
  assume imo72b2lem1.1: |- ( ph -> F : RR --> RR )
  assume imo72b2lem1.7: |- ( ph -> E. x e. RR ( F ` x ) =/= 0 )
  assume imo72b2lem1.6: |- ( ph -> A. y e. RR ( abs ` ( F ` y ) ) <_ 1 )

  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint F c
  disjoint F t
  disjoint c t
  disjoint F z
  disjoint x z
  disjoint t y
  disjoint c ph
  disjoint ph t
  disjoint ph z
  assert |- ( ph -> 0 < sup ( ( abs " ( F " RR ) ) , RR , < ) )

  proof
    wph
    vc
    vt
    vz
    cabs
    cF
    cr
    cima
    cima
    #
    cc0
    wph
    @0
    cabs
    cF
    ccom
    #
    cr
    cima
    #
    cr
    @2
    @0
    cabs
    cF
    cr
    imaco
    #
    eqcomi
    #
    wph
    @2
    @1
    crn
    #
    cr
    @2
    @5
    wss
    wph
    @1
    cr
    imassrn
    a1i
    wph
    cr
    cr
    @1
    wf
    @5
    cr
    wss
    wph
    cr
    cr
    cr
    cabs
    cF
    imo72b2lem1.1
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
    #
    cr
    cr
    @1
    frn
    syl
    sstrd
    syl5eqss
    wph
    c0
    @0
    wph
    c0
    @2
    @0
    wph
    @2
    c0
    wph
    cr
    cr
    @1
    cr
    c0
    wne
    wph
    cc0
    cr
    0re
    ne0ii
    a1i
    @6
    wnefimgd
    necomd
    @0
    @2
    wceq
    wph
    @4
    a1i
    neeqtrrd
    necomd
    wph
    vt
    cv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vt
    @0
    wral
    @7
    c1
    cle
    wbr
    #
    vt
    @0
    wral
    vc
    c1
    cr
    wph
    1red
    wph
    @8
    c1
    wceq
    #
    wa
    #
    @9
    @10
    vt
    @0
    @12
    @8
    c1
    @7
    cle
    wph
    @11
    simpr
    breq2d
    ralbidv
    wph
    vt
    vy
    c1
    cF
    imo72b2lem1.1
    imo72b2lem1.6
    extoimad
    rspcedvd
    wph
    0red
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wne
    #
    cc0
    vz
    cv
    #
    clt
    wbr
    #
    vz
    @0
    wrex
    vx
    cr
    imo72b2lem1.7
    wph
    @13
    cr
    wcel
    #
    @15
    wa
    #
    wa
    #
    @17
    cc0
    @14
    cabs
    cfv
    #
    clt
    wbr
    vz
    @21
    @0
    @20
    @13
    @1
    cfv
    #
    @21
    @0
    @20
    cr
    cr
    @13
    cabs
    cF
    wph
    cr
    cr
    cF
    wf
    @19
    imo72b2lem1.1
    adantr
    wph
    @18
    @15
    simprl
    fvco3d
    @20
    @22
    @2
    @0
    wph
    @18
    @22
    @2
    wcel
    @15
    wph
    vx
    cr
    cr
    @1
    @6
    funfvima2d
    adantrr
    @3
    syl6eleq
    eqeltrrd
    @20
    @16
    @21
    wceq
    #
    wa
    @16
    @21
    cc0
    clt
    @20
    @23
    simpr
    breq2d
    @20
    @21
    @20
    @14
    @20
    @14
    wph
    @18
    @14
    cr
    wcel
    @15
    wph
    cr
    cr
    @13
    cF
    imo72b2lem1.1
    ffvelrnda
    adantrr
    recnd
    wph
    @18
    @15
    simprr
    absrpcld
    rpgt0d
    rspcedvd
    rexlimddv
    suprlubrd
end
