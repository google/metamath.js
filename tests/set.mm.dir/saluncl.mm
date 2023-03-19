include "csalg.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cpr.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "uniprg.mm"
include "eqcomd.mm"
include "3adant1.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cfn.mm"
include "prfi.mm"
include "csdm.mm"
include "isfinite.mm"
include "biimpi.mm"
include "sdomdom.mm"
include "syl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "prelpwi.mm"
include "c0.mm"
include "cdif.mm"
include "issal.mm"
include "ibi.mm"
include "simp3d.mm"
include "3ad2ant1.mm"
include "breq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "mpd.mm"
include "eqeltrd.mm"

theorem saluncl
  let cS: class S
  let cE: class E
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. SAlg /\ E e. S /\ F e. S ) -> ( E u. F ) e. S )

  proof
    cS
    csalg
    wcel
    #
    cE
    cS
    wcel
    #
    cF
    cS
    wcel
    #
    w3a
    #
    cE
    cF
    cun
    #
    cE
    cF
    cpr
    #
    cuni
    #
    cS
    @1
    @2
    @4
    @6
    wceq
    @0
    @1
    @2
    wa
    @6
    @4
    cE
    cF
    cS
    cS
    uniprg
    eqcomd
    3adant1
    @3
    @5
    com
    cdom
    wbr
    #
    @6
    cS
    wcel
    #
    @7
    @3
    @5
    cfn
    wcel
    #
    @7
    cE
    cF
    prfi
    @9
    @5
    com
    csdm
    wbr
    #
    @7
    @9
    @10
    @5
    isfinite
    biimpi
    @5
    com
    sdomdom
    syl
    ax-mp
    a1i
    @3
    @5
    cS
    cpw
    #
    wcel
    #
    vy
    cv
    #
    com
    cdom
    wbr
    #
    @13
    cuni
    #
    cS
    wcel
    #
    wi
    #
    vy
    @11
    wral
    #
    @7
    @8
    wi
    #
    @1
    @2
    @12
    @0
    cE
    cF
    cS
    prelpwi
    3adant1
    @0
    @1
    @18
    @2
    @0
    c0
    cS
    wcel
    #
    cS
    cuni
    @13
    cdif
    cS
    wcel
    vy
    cS
    wral
    #
    @18
    @0
    @20
    @21
    @18
    w3a
    vy
    cS
    csalg
    issal
    ibi
    simp3d
    3ad2ant1
    @17
    @19
    vy
    @5
    @11
    @13
    @5
    wceq
    #
    @14
    @7
    @16
    @8
    @13
    @5
    com
    cdom
    breq1
    @22
    @15
    @6
    cS
    @13
    @5
    unieq
    eleq1d
    imbi12d
    rspcva
    syl2anc
    mpd
    eqeltrd
end
