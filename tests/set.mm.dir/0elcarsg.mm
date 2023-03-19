include "c0.mm"
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
include "0ss.mm"
include "a1i.mm"
include "wa.mm"
include "cc0.mm"
include "in0.mm"
include "fveq2i.mm"
include "syl5eq.mm"
include "dif0.mm"
include "oveq12d.mm"
include "adantr.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "xaddid2.mm"
include "syl.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "elcarsg.mm"
include "mpbir2and.mm"

theorem 0elcarsg
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


  assert |- ( ph -> (/) e. ( toCaraSiga ` M ) )

  proof
    wph
    c0
    cM
    ccarsg
    cfv
    wcel
    c0
    cO
    wss
    #
    ve
    cv
    #
    c0
    cin
    #
    cM
    cfv
    #
    @1
    c0
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
    @0
    wph
    cO
    0ss
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
    cc0
    @7
    cxad
    co
    #
    @7
    wph
    @6
    @12
    wceq
    @10
    wph
    @3
    cc0
    @5
    @7
    cxad
    wph
    @3
    c0
    cM
    cfv
    cc0
    @2
    c0
    cM
    @1
    in0
    fveq2i
    baselcarsg.1
    syl5eq
    @5
    @7
    wceq
    wph
    @4
    @1
    cM
    @1
    dif0
    fveq2i
    a1i
    oveq12d
    adantr
    @11
    @7
    cxr
    wcel
    @12
    @7
    wceq
    @11
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
    wph
    @9
    @13
    @1
    cM
    carsgval.2
    ffvelrnda
    sseldi
    @7
    xaddid2
    syl
    eqtrd
    ralrimiva
    wph
    c0
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbir2and
end
