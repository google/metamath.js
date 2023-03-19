include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "w3a.mm"
include "df-icc.mm"
include "elixx3g.mm"
include "simplbi.mm"
include "adantr.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simprbi.mm"
include "simpld.mm"
include "simprd.mm"
include "adantl.mm"
include "cv.mm"
include "xrletr.mm"
include "ixxss12.mm"
include "syl22anc.mm"

theorem iccss2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( C e. ( A [,] B ) /\ D e. ( A [,] B ) ) -> ( C [,] D ) C_ ( A [,] B ) )

  proof
    cC
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
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
    cle
    wbr
    #
    cC
    cD
    cicc
    co
    @0
    wss
    @3
    @4
    @5
    cC
    cxr
    wcel
    #
    @1
    @4
    @5
    @8
    w3a
    #
    @2
    @1
    @9
    @6
    cC
    cB
    cle
    wbr
    #
    wa
    #
    vx
    vy
    vz
    cA
    cB
    cC
    cle
    cle
    cicc
    vx
    vy
    vz
    df-icc
    #
    elixx3g
    #
    simplbi
    adantr
    #
    simp1d
    @3
    @4
    @5
    @8
    @14
    simp2d
    @3
    @6
    @10
    @1
    @11
    @2
    @1
    @9
    @11
    @13
    simprbi
    adantr
    simpld
    @2
    @7
    @1
    @2
    cA
    cD
    cle
    wbr
    #
    @7
    @2
    @4
    @5
    cD
    cxr
    wcel
    w3a
    @15
    @7
    wa
    vx
    vy
    vz
    cA
    cB
    cD
    cle
    cle
    cicc
    @12
    elixx3g
    simprbi
    simprd
    adantl
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cicc
    cle
    cle
    cle
    cle
    cicc
    cle
    cle
    @12
    @12
    cA
    cC
    vw
    cv
    #
    xrletr
    @16
    cD
    cB
    xrletr
    ixxss12
    syl22anc
end
