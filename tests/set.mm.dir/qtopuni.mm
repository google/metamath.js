include "ctop.mm"
include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "cqtop.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "ssid.mm"
include "a1i.mm"
include "wf.mm"
include "wceq.mm"
include "fof.mm"
include "adantl.mm"
include "fimacnv.mm"
include "syl.mm"
include "topopn.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "elqtop2.mm"
include "mpbir2and.mm"
include "elssuni.mm"
include "cpw.mm"
include "cv.mm"
include "simpl.mm"
include "selpw.mm"
include "sylibr.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "sspwuni.mm"
include "sylib.mm"
include "eqssd.mm"

theorem qtopuni
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  assume qtoptop.1: |- X = U. J


  assert |- ( ( J e. Top /\ F : X -onto-> Y ) -> Y = U. ( J qTop F ) )

  proof
    cJ
    ctop
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    wa
    #
    cY
    cJ
    cF
    cqtop
    co
    #
    cuni
    #
    @2
    cY
    @3
    wcel
    #
    cY
    @4
    wss
    @2
    @5
    cY
    cY
    wss
    #
    cF
    ccnv
    #
    cY
    cima
    #
    cJ
    wcel
    @6
    @2
    cY
    ssid
    a1i
    @2
    @8
    cX
    cJ
    @2
    cX
    cY
    cF
    wf
    #
    @8
    cX
    wceq
    @1
    @9
    @0
    cX
    cY
    cF
    fof
    adantl
    cX
    cY
    cF
    fimacnv
    syl
    @0
    cX
    cJ
    wcel
    @1
    cJ
    cX
    qtoptop.1
    topopn
    adantr
    eqeltrd
    cY
    cF
    cJ
    ctop
    cX
    cY
    qtoptop.1
    elqtop2
    mpbir2and
    cY
    @3
    elssuni
    syl
    @2
    @3
    cY
    cpw
    #
    wss
    @4
    cY
    wss
    @2
    vx
    @3
    @10
    @2
    vx
    cv
    #
    @3
    wcel
    @11
    cY
    wss
    #
    @7
    @11
    cima
    cJ
    wcel
    #
    wa
    #
    @11
    @10
    wcel
    #
    @11
    cF
    cJ
    ctop
    cX
    cY
    qtoptop.1
    elqtop2
    @14
    @12
    @15
    @12
    @13
    simpl
    vx
    cY
    selpw
    sylibr
    syl6bi
    ssrdv
    @3
    cY
    sspwuni
    sylib
    eqssd
end
