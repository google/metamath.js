include "cnv.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "adantr.mm"
include "nvs.mm"
include "syl3an2.mm"
include "absid.mm"
include "3ad2ant2.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem nvsge0
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cN: class N
  let cX: class X
  let vy: setvar y
  let vx: setvar x
  assume nvs.1: |- X = ( BaseSet ` U )
  assume nvs.4: |- S = ( .sOLD ` U )
  assume nvs.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. RR /\ 0 <_ A ) /\ B e. X ) -> ( N ` ( A S B ) ) = ( A x. ( N ` B ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cS
    co
    cN
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cN
    cfv
    #
    cmul
    co
    #
    cA
    @8
    cmul
    co
    @3
    @0
    cA
    cc
    wcel
    #
    @4
    @6
    @9
    wceq
    @1
    @10
    @2
    cA
    recn
    adantr
    cA
    cB
    cS
    cU
    cN
    cX
    nvs.1
    nvs.4
    nvs.6
    nvs
    syl3an2
    @5
    @7
    cA
    @8
    cmul
    @3
    @0
    @7
    cA
    wceq
    @4
    cA
    absid
    3ad2ant2
    oveq1d
    eqtrd
end
