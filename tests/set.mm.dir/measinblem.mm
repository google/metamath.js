include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wdisj.mm"
include "cuni.mm"
include "cin.mm"
include "ciun.mm"
include "cesum.mm"
include "iunin1.mm"
include "uniiun.mm"
include "ineq1i.mm"
include "eqtr4i.mm"
include "fveq2i.mm"
include "wral.mm"
include "wceq.mm"
include "simplll.mm"
include "nfv.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "w3a.mm"
include "csiga.mm"
include "crn.mm"
include "simp1ll.mm"
include "measbase.mm"
include "syl.mm"
include "simp3.mm"
include "simp1r.mm"
include "elelpwi.mm"
include "syl2anc.mm"
include "simp1lr.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "3expia.mm"
include "ralrimi.mm"
include "simprl.mm"
include "disjin.mm"
include "ad2antll.mm"
include "measvuni.mm"
include "syl112anc.mm"
include "syl5eqr.mm"

theorem measinblem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint S x
  disjoint M x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint S y
  disjoint S z
  disjoint M y
  disjoint M z
  assert |- ( ( ( ( M e. ( measures ` S ) /\ A e. S ) /\ B e. ~P S ) /\ ( B ~<_ _om /\ Disj_ x e. B x ) ) -> ( M ` ( U. B i^i A ) ) = sum* x e. B ( M ` ( x i^i A ) ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cA
    cS
    wcel
    #
    wa
    #
    cB
    cS
    cpw
    wcel
    #
    wa
    #
    cB
    com
    cdom
    wbr
    #
    vx
    cB
    vx
    cv
    #
    wdisj
    #
    wa
    #
    wa
    #
    cB
    cuni
    #
    cA
    cin
    #
    cM
    cfv
    vx
    cB
    @6
    cA
    cin
    #
    ciun
    #
    cM
    cfv
    #
    cB
    @12
    cM
    cfv
    vx
    cesum
    #
    @13
    @11
    cM
    @13
    vx
    cB
    @6
    ciun
    #
    cA
    cin
    @11
    vx
    cB
    cA
    @6
    iunin1
    @10
    @16
    cA
    vx
    cB
    uniiun
    ineq1i
    eqtr4i
    fveq2i
    @9
    @0
    @12
    cS
    wcel
    #
    vx
    cB
    wral
    @5
    vx
    cB
    @12
    wdisj
    #
    @14
    @15
    wceq
    @0
    @1
    @3
    @8
    simplll
    @9
    @17
    vx
    cB
    @4
    @8
    vx
    @4
    vx
    nfv
    @5
    @7
    vx
    @5
    vx
    nfv
    vx
    cB
    @6
    nfdisj1
    nfan
    nfan
    @4
    @8
    @6
    cB
    wcel
    #
    @17
    @4
    @8
    @19
    w3a
    #
    cS
    csiga
    crn
    cuni
    wcel
    #
    @6
    cS
    wcel
    #
    @1
    @17
    @20
    @0
    @21
    @0
    @1
    @3
    @8
    @19
    simp1ll
    cS
    cM
    measbase
    syl
    @20
    @19
    @3
    @22
    @4
    @8
    @19
    simp3
    @2
    @3
    @8
    @19
    simp1r
    @6
    cB
    cS
    elelpwi
    syl2anc
    @0
    @1
    @3
    @8
    @19
    simp1lr
    @6
    cA
    cS
    inelsiga
    syl3anc
    3expia
    ralrimi
    @4
    @5
    @7
    simprl
    @7
    @18
    @4
    @5
    vx
    cA
    cB
    @6
    disjin
    ad2antll
    vx
    cB
    @12
    cS
    cM
    measvuni
    syl112anc
    syl5eqr
end
