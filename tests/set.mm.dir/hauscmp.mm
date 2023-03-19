include "cha.mm"
include "wcel.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "w3a.mm"
include "ccld.mm"
include "cfv.mm"
include "cdif.mm"
include "simp2.mm"
include "wel.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "ccl.mm"
include "crab.mm"
include "eqid.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "hauscmplem.mm"
include "wi.mm"
include "ctop.mm"
include "haustop.mm"
include "3ad2ant1.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "sscls.mm"
include "syl2an.mm"
include "sstr2.mm"
include "syl.mm"
include "anim2d.mm"
include "reximdva.mm"
include "adantr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "eltop2.mm"
include "mpbird.mm"
include "iscld.mm"
include "mpbir2and.mm"

theorem hauscmp
  let cS: class S
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let wph: wff ph
  let cO: class O
  assume hauscmp.1: |- X = U. J


  assert |- ( ( J e. Haus /\ S C_ X /\ ( J |`t S ) e. Comp ) -> S e. ( Clsd ` J ) )

  proof
    cJ
    cha
    wcel
    #
    cS
    cX
    wss
    #
    cJ
    cS
    crest
    co
    ccmp
    wcel
    #
    w3a
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    @1
    cX
    cS
    cdif
    #
    cJ
    wcel
    #
    @0
    @1
    @2
    simp2
    @3
    @6
    vx
    vz
    wel
    #
    vz
    cv
    #
    @5
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    vx
    @5
    wral
    #
    @3
    @11
    vx
    @5
    @3
    vx
    cv
    #
    @5
    wcel
    #
    wa
    #
    @7
    @8
    cJ
    ccl
    cfv
    #
    cfv
    #
    @5
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    @11
    @15
    vy
    vz
    vw
    @13
    cS
    cJ
    vx
    vw
    wel
    vw
    cv
    @16
    cfv
    cX
    vy
    cv
    cdif
    wss
    wa
    vw
    cJ
    wrex
    vy
    cJ
    crab
    #
    cX
    hauscmp.1
    @21
    eqid
    @0
    @1
    @2
    @14
    simpl1
    @0
    @1
    @2
    @14
    simpl2
    @0
    @1
    @2
    @14
    simpl3
    @3
    @14
    simpr
    hauscmplem
    @3
    @20
    @11
    wi
    @14
    @3
    @19
    @10
    vz
    cJ
    @3
    @8
    cJ
    wcel
    #
    wa
    #
    @18
    @9
    @7
    @23
    @8
    @17
    wss
    #
    @18
    @9
    wi
    @3
    cJ
    ctop
    wcel
    #
    @8
    cX
    wss
    @24
    @22
    @0
    @1
    @25
    @2
    cJ
    haustop
    3ad2ant1
    #
    @22
    @8
    cJ
    cuni
    cX
    @8
    cJ
    elssuni
    hauscmp.1
    syl6sseqr
    @8
    cJ
    cX
    hauscmp.1
    sscls
    syl2an
    @8
    @17
    @5
    sstr2
    syl
    anim2d
    reximdva
    adantr
    mpd
    ralrimiva
    @3
    @25
    @6
    @12
    wb
    @26
    vx
    vz
    @5
    cJ
    eltop2
    syl
    mpbird
    @3
    @25
    @4
    @1
    @6
    wa
    wb
    @26
    cS
    cJ
    cX
    hauscmp.1
    iscld
    syl
    mpbir2and
end
