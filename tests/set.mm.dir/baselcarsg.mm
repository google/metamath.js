include "ccarsg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "ssid.mm"
include "a1i.mm"
include "cc0.mm"
include "elpwi.mm"
include "adantl.mm"
include "df-ss.mm"
include "sylib.mm"
include "fveq2d.mm"
include "c0.mm"
include "ssdif0.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wf.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "xaddid1.mm"
include "syl.mm"
include "ralrimiva.mm"
include "jca.mm"
include "elcarsg.mm"
include "mpbird.mm"

theorem baselcarsg
  let wph: wff ph
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let cA: class A
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume baselcarsg.1: |- ( ph -> ( M ` (/) ) = 0 )


  assert |- ( ph -> O e. ( toCaraSiga ` M ) )

  proof
    wph
    cO
    cM
    ccarsg
    cfv
    wcel
    cO
    cO
    wss
    #
    ve
    cv
    #
    cO
    cin
    #
    cM
    cfv
    #
    @1
    cO
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @1
    cM
    cfv
    #
    wceq
    #
    ve
    cO
    cpw
    #
    wral
    #
    wa
    wph
    @0
    @10
    @0
    wph
    cO
    ssid
    a1i
    wph
    @8
    ve
    @9
    wph
    @1
    @9
    wcel
    #
    wa
    #
    @6
    @7
    cc0
    cxad
    co
    #
    @7
    @12
    @3
    @7
    @5
    cc0
    cxad
    @12
    @2
    @1
    cM
    @12
    @1
    cO
    wss
    #
    @2
    @1
    wceq
    @11
    @14
    wph
    @1
    cO
    elpwi
    adantl
    #
    @1
    cO
    df-ss
    sylib
    fveq2d
    @12
    @5
    c0
    cM
    cfv
    #
    cc0
    @12
    @4
    c0
    cM
    @12
    @14
    @4
    c0
    wceq
    @15
    @1
    cO
    ssdif0
    sylib
    fveq2d
    wph
    @16
    cc0
    wceq
    @11
    baselcarsg.1
    adantr
    eqtrd
    oveq12d
    @12
    @7
    cxr
    wcel
    @13
    @7
    wceq
    @12
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @7
    cc0
    cpnf
    iccssxr
    @12
    @9
    @17
    @1
    cM
    wph
    @9
    @17
    cM
    wf
    @11
    carsgval.2
    adantr
    wph
    @11
    simpr
    ffvelrnd
    sseldi
    @7
    xaddid1
    syl
    eqtrd
    ralrimiva
    jca
    wph
    cO
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbird
end
