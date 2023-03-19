include "cico.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cicc.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "df-ico.mm"
include "elmpt2cl1.mm"
include "adantr.mm"
include "elmpt2cl2.mm"
include "w3a.mm"
include "elixx3g.mm"
include "simprbi.mm"
include "simpld.mm"
include "simprd.mm"
include "adantl.mm"
include "iccssico.mm"
include "syl22anc.mm"

theorem iccssico2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( C e. ( A [,) B ) /\ D e. ( A [,) B ) ) -> ( C [,] D ) C_ ( A [,) B ) )

  proof
    cC
    cA
    cB
    cico
    co
    #
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cD
    cB
    clt
    wbr
    #
    cC
    cD
    cicc
    co
    @0
    wss
    @1
    @3
    @2
    vx
    vy
    cxr
    cxr
    vx
    cv
    vz
    cv
    #
    cle
    wbr
    @7
    vy
    cv
    clt
    wbr
    wa
    vz
    cxr
    crab
    #
    cA
    cB
    cico
    cC
    vx
    vy
    vz
    df-ico
    #
    elmpt2cl1
    adantr
    @1
    @4
    @2
    vx
    vy
    cxr
    cxr
    @8
    cA
    cB
    cico
    cC
    @9
    elmpt2cl2
    adantr
    @1
    @5
    @2
    @1
    @5
    cC
    cB
    clt
    wbr
    #
    @1
    @3
    @4
    cC
    cxr
    wcel
    w3a
    @5
    @10
    wa
    vx
    vy
    vz
    cA
    cB
    cC
    cle
    clt
    cico
    @9
    elixx3g
    simprbi
    simpld
    adantr
    @2
    @6
    @1
    @2
    cA
    cD
    cle
    wbr
    #
    @6
    @2
    @3
    @4
    cD
    cxr
    wcel
    w3a
    @11
    @6
    wa
    vx
    vy
    vz
    cA
    cB
    cD
    cle
    clt
    cico
    @9
    elixx3g
    simprbi
    simprd
    adantl
    cA
    cB
    cC
    cD
    iccssico
    syl22anc
end
