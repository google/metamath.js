include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "neg1cn.mm"
include "nvs.mm"
include "mp3an2.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "nvcl.mm"
include "recnd.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem nvm1
  let cA: class A
  let cS: class S
  let cU: class U
  let cN: class N
  let cX: class X
  let vy: setvar y
  let vx: setvar x
  let cB: class B
  assume nvs.1: |- X = ( BaseSet ` U )
  assume nvs.4: |- S = ( .sOLD ` U )
  assume nvs.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` ( -u 1 S A ) ) = ( N ` A ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    c1
    cneg
    #
    cA
    cS
    co
    cN
    cfv
    #
    @3
    cabs
    cfv
    #
    cA
    cN
    cfv
    #
    cmul
    co
    #
    @6
    @0
    @3
    cc
    wcel
    @1
    @4
    @7
    wceq
    neg1cn
    @3
    cA
    cS
    cU
    cN
    cX
    nvs.1
    nvs.4
    nvs.6
    nvs
    mp3an2
    @2
    @7
    c1
    @6
    cmul
    co
    @6
    @5
    c1
    @6
    cmul
    @5
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    @2
    @6
    @2
    @6
    cA
    cU
    cN
    cX
    nvs.1
    nvs.6
    nvcl
    recnd
    mulid2d
    syl5eq
    eqtrd
end
