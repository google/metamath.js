include "cabs.mm"
include "cr.mm"
include "cima.mm"
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
include "cc0.mm"
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
include "wa.mm"
include "simpr.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "extoimad.mm"
include "rspcedvd.mm"
include "suprleubrd.mm"

theorem imo72b2lem2
  let wph: wff ph
  let vz: setvar z
  let cC: class C
  let cF: class F
  let vc: setvar c
  let vv: setvar v
  let vt: setvar t
  assume imo72b2lem2.1: |- ( ph -> F : RR --> RR )
  assume imo72b2lem2.2: |- ( ph -> C e. RR )
  assume imo72b2lem2.3: |- ( ph -> A. z e. RR ( abs ` ( F ` z ) ) <_ C )

  disjoint C z
  disjoint F z
  disjoint ph z
  disjoint C c
  disjoint C v
  disjoint c v
  disjoint c z
  disjoint v z
  disjoint C t
  disjoint t z
  disjoint F c
  disjoint F v
  disjoint F t
  disjoint c ph
  disjoint ph v
  disjoint ph t
  assert |- ( ph -> sup ( ( abs " ( F " RR ) ) , RR , < ) <_ C )

  proof
    wph
    vc
    vv
    vt
    cabs
    cF
    cr
    cima
    cima
    #
    cC
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
    eqcomi
    #
    wph
    @2
    @1
    crn
    #
    cr
    @2
    @4
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
    @4
    cr
    wss
    wph
    cr
    cr
    cr
    cabs
    cF
    imo72b2lem2.1
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
    @5
    wnefimgd
    necomd
    @0
    @2
    wceq
    wph
    @3
    a1i
    neeqtrrd
    necomd
    wph
    vv
    cv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vv
    @0
    wral
    @6
    cC
    cle
    wbr
    #
    vv
    @0
    wral
    vc
    cC
    cr
    imo72b2lem2.2
    wph
    @7
    cC
    wceq
    #
    wa
    #
    @8
    @9
    vv
    @0
    @11
    @7
    cC
    @6
    cle
    wph
    @10
    simpr
    breq2d
    ralbidv
    wph
    vv
    vz
    cC
    cF
    imo72b2lem2.1
    imo72b2lem2.3
    extoimad
    rspcedvd
    imo72b2lem2.2
    wph
    vt
    vz
    cC
    cF
    imo72b2lem2.1
    imo72b2lem2.3
    extoimad
    suprleubrd
end
