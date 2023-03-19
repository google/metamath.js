include "ctsu.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cres.mm"
include "cgsu.mm"
include "wi.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "ctopn.mm"
include "cfv.mm"
include "wa.mm"
include "eqid.mm"
include "eltsms.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ssrdv.mm"

theorem tsmscl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cJ: class J
  assume tsmscl.b: |- B = ( Base ` G )
  assume tsmscl.1: |- ( ph -> G e. CMnd )
  assume tsmscl.2: |- ( ph -> G e. TopSp )
  assume tsmscl.a: |- ( ph -> A e. V )
  assume tsmscl.f: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( G tsums F ) C_ B )

  proof
    wph
    vx
    cG
    cF
    ctsu
    co
    #
    cB
    wph
    vx
    cv
    #
    @0
    wcel
    @1
    cB
    wcel
    #
    @1
    vw
    cv
    #
    wcel
    vz
    cv
    vy
    cv
    #
    wss
    cG
    cF
    @4
    cres
    cgsu
    co
    @3
    wcel
    wi
    vy
    cA
    cpw
    cfn
    cin
    #
    wral
    vz
    @5
    wrex
    wi
    vw
    cG
    ctopn
    cfv
    #
    wral
    #
    wa
    @2
    wph
    vy
    vz
    vw
    cA
    cB
    @1
    @5
    cF
    cG
    @6
    cV
    tsmscl.b
    @6
    eqid
    @5
    eqid
    tsmscl.1
    tsmscl.2
    tsmscl.a
    tsmscl.f
    eltsms
    @2
    @7
    simpl
    syl6bi
    ssrdv
end
