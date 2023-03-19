include "wcel.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "csigagen.mm"
include "cfv.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "simp1.mm"
include "sgsiga.mm"
include "sssigagen.mm"
include "sspwb.mm"
include "biimpi.mm"
include "3syl.mm"
include "simp2.mm"
include "cvv.mm"
include "wb.mm"
include "simp3.mm"
include "ctex.mm"
include "elpwg.mm"
include "mpbird.mm"
include "sseldd.mm"
include "sigaclcu.mm"
include "syl3anc.mm"

theorem elsigagen2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. V /\ B C_ A /\ B ~<_ _om ) -> U. B e. ( sigaGen ` A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    wss
    #
    cB
    com
    cdom
    wbr
    #
    w3a
    #
    cA
    csigagen
    cfv
    #
    csiga
    crn
    cuni
    wcel
    cB
    @4
    cpw
    #
    wcel
    @2
    cB
    cuni
    @4
    wcel
    @3
    cA
    cV
    @0
    @1
    @2
    simp1
    #
    sgsiga
    @3
    cA
    cpw
    #
    @5
    cB
    @3
    @0
    cA
    @4
    wss
    #
    @7
    @5
    wss
    #
    @6
    cA
    cV
    sssigagen
    @8
    @9
    cA
    @4
    sspwb
    biimpi
    3syl
    @3
    cB
    @7
    wcel
    #
    @1
    @0
    @1
    @2
    simp2
    @3
    @2
    cB
    cvv
    wcel
    @10
    @1
    wb
    @0
    @1
    @2
    simp3
    #
    cB
    ctex
    cB
    cA
    cvv
    elpwg
    3syl
    mpbird
    sseldd
    @11
    cB
    @4
    sigaclcu
    syl3anc
end
