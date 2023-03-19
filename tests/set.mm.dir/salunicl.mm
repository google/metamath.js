include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "c0.mm"
include "cdif.mm"
include "csalg.mm"
include "w3a.mm"
include "wb.mm"
include "issal.mm"
include "syl.mm"
include "mpbid.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem salunicl
  let wph: wff ph
  let cS: class S
  let cT: class T
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume salunicl.s: |- ( ph -> S e. SAlg )
  assume salunicl.t: |- ( ph -> T e. ~P S )
  assume salunicl.tct: |- ( ph -> T ~<_ _om )


  assert |- ( ph -> U. T e. S )

  proof
    wph
    cT
    com
    cdom
    wbr
    #
    cT
    cuni
    #
    cS
    wcel
    #
    salunicl.tct
    wph
    cT
    cS
    cpw
    #
    wcel
    vy
    cv
    #
    com
    cdom
    wbr
    #
    @4
    cuni
    #
    cS
    wcel
    #
    wi
    #
    vy
    @3
    wral
    #
    @0
    @2
    wi
    #
    salunicl.t
    wph
    c0
    cS
    wcel
    #
    cS
    cuni
    @4
    cdif
    cS
    wcel
    vy
    cS
    wral
    #
    @9
    wph
    cS
    csalg
    wcel
    #
    @11
    @12
    @9
    w3a
    #
    salunicl.s
    wph
    @13
    @13
    @14
    wb
    salunicl.s
    vy
    cS
    csalg
    issal
    syl
    mpbid
    simp3d
    @8
    @10
    vy
    cT
    @3
    @4
    cT
    wceq
    #
    @5
    @0
    @7
    @2
    @4
    cT
    com
    cdom
    breq1
    @15
    @6
    @1
    cS
    @4
    cT
    unieq
    eleq1d
    imbi12d
    rspcva
    syl2anc
    mpd
end
