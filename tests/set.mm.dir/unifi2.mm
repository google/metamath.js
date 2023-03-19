include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "isfinite2.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "unifi.mm"
include "syl2an.mm"
include "cvv.mm"
include "wb.mm"
include "fin2inf.mm"
include "adantr.mm"
include "isfiniteg.mm"
include "syl.mm"
include "mpbid.mm"

theorem unifi2
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( A ~< _om /\ A. x e. A x ~< _om ) -> U. A ~< _om )

  proof
    cA
    com
    csdm
    wbr
    #
    vx
    cv
    #
    com
    csdm
    wbr
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    cuni
    #
    cfn
    wcel
    #
    @5
    com
    csdm
    wbr
    #
    @0
    cA
    cfn
    wcel
    cA
    cfn
    wss
    #
    @6
    @3
    cA
    isfinite2
    @3
    @1
    cfn
    wcel
    #
    vx
    cA
    wral
    @8
    @2
    @9
    vx
    cA
    @1
    isfinite2
    ralimi
    vx
    cA
    cfn
    dfss3
    sylibr
    cA
    unifi
    syl2an
    @4
    com
    cvv
    wcel
    #
    @6
    @7
    wb
    @0
    @10
    @3
    cA
    fin2inf
    adantr
    @5
    isfiniteg
    syl
    mpbid
end
