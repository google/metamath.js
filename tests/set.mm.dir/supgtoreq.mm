include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "csup.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"
include "fisup2g.mm"
include "syl13anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "supub.mm"
include "mpd.mm"
include "breq1d.mm"
include "mtbird.mm"
include "wb.mm"
include "fisupcl.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "sotric.mm"
include "syl12anc.mm"
include "orcom.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6rbb.mm"
include "notnotrd.mm"

theorem supgtoreq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume supgtoreq.1: |- ( ph -> R Or A )
  assume supgtoreq.2: |- ( ph -> B C_ A )
  assume supgtoreq.3: |- ( ph -> B e. Fin )
  assume supgtoreq.4: |- ( ph -> C e. B )
  assume supgtoreq.5: |- ( ph -> S = sup ( B , A , R ) )


  assert |- ( ph -> ( C R S \/ C = S ) )

  proof
    wph
    cC
    cS
    cR
    wbr
    #
    cC
    cS
    wceq
    #
    wo
    #
    wph
    @2
    wn
    #
    cS
    cC
    cR
    wbr
    #
    wph
    @4
    cB
    cA
    cR
    csup
    #
    cC
    cR
    wbr
    #
    wph
    cC
    cB
    wcel
    #
    @6
    wn
    supgtoreq.4
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    supgtoreq.1
    wph
    cB
    cA
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    @10
    @9
    cR
    wbr
    @10
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    wi
    vy
    cA
    wral
    wa
    #
    vx
    cB
    wrex
    #
    @11
    vx
    cA
    wrex
    supgtoreq.2
    wph
    cA
    cR
    wor
    #
    cB
    cfn
    wcel
    #
    cB
    c0
    wne
    #
    @8
    @12
    supgtoreq.1
    supgtoreq.3
    wph
    @7
    @15
    supgtoreq.4
    cB
    cC
    ne0i
    syl
    #
    supgtoreq.2
    vx
    vy
    vz
    cA
    cB
    cR
    fisup2g
    syl13anc
    @11
    vx
    cB
    cA
    ssrexv
    sylc
    supub
    mpd
    wph
    cS
    @5
    cC
    cR
    supgtoreq.5
    breq1d
    mtbird
    wph
    @4
    cS
    cC
    wceq
    #
    @0
    wo
    #
    wn
    #
    @3
    wph
    @13
    cS
    cA
    wcel
    cC
    cA
    wcel
    @4
    @19
    wb
    supgtoreq.1
    wph
    cS
    @5
    cA
    supgtoreq.5
    wph
    cB
    cA
    @5
    supgtoreq.2
    wph
    @13
    @14
    @15
    @8
    @5
    cB
    wcel
    supgtoreq.1
    supgtoreq.3
    @16
    supgtoreq.2
    cA
    cB
    cR
    fisupcl
    syl13anc
    sseldd
    eqeltrd
    wph
    cB
    cA
    cC
    supgtoreq.2
    supgtoreq.4
    sseldd
    cA
    cS
    cC
    cR
    sotric
    syl12anc
    @18
    @2
    @18
    @0
    @17
    wo
    @2
    @17
    @0
    orcom
    @17
    @1
    @0
    cS
    cC
    eqcom
    orbi2i
    bitri
    notbii
    syl6rbb
    mtbird
    notnotrd
end
