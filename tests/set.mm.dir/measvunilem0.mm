include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "w3a.mm"
include "cc0.mm"
include "cesum.mm"
include "ciun.mm"
include "cvv.mm"
include "wceq.mm"
include "simp3l.mm"
include "ctex.mm"
include "esum0.mm"
include "3syl.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "nf3an.mm"
include "eqidd.mm"
include "cv.mm"
include "simp2.mm"
include "r19.21bi.mm"
include "elsni.mm"
include "syl.mm"
include "fveq2d.mm"
include "measvnul.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "esumeq12dvaf.mm"
include "iuneq12daf.mm"
include "iun0.mm"
include "syl6eq.mm"
include "3eqtr4rd.mm"

theorem measvunilem0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  assume measvunilem.0.1: |- F/_ x A

  disjoint M x
  disjoint S x
  assert |- ( ( M e. ( measures ` S ) /\ A. x e. A B e. { (/) } /\ ( A ~<_ _om /\ Disj_ x e. A B ) ) -> ( M ` U_ x e. A B ) = sum* x e. A ( M ` B ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cB
    c0
    csn
    wcel
    #
    vx
    cA
    wral
    #
    cA
    com
    cdom
    wbr
    #
    vx
    cA
    cB
    wdisj
    #
    wa
    #
    w3a
    #
    cA
    cc0
    vx
    cesum
    #
    cc0
    cA
    cB
    cM
    cfv
    #
    vx
    cesum
    vx
    cA
    cB
    ciun
    #
    cM
    cfv
    #
    @6
    @3
    cA
    cvv
    wcel
    @7
    cc0
    wceq
    @0
    @2
    @3
    @4
    simp3l
    cA
    ctex
    cA
    vx
    cvv
    measvunilem.0.1
    esum0
    3syl
    @6
    cA
    cA
    @8
    cc0
    vx
    @0
    @2
    @5
    vx
    @0
    vx
    nfv
    @1
    vx
    cA
    nfra1
    @3
    @4
    vx
    vx
    cA
    com
    cdom
    measvunilem.0.1
    vx
    cdom
    nfcv
    vx
    com
    nfcv
    nfbr
    vx
    cA
    cB
    nfdisj1
    nfan
    nf3an
    #
    @6
    cA
    eqidd
    #
    @6
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @8
    c0
    cM
    cfv
    #
    cc0
    @14
    cB
    c0
    cM
    @14
    @1
    cB
    c0
    wceq
    @6
    @1
    vx
    cA
    @0
    @2
    @5
    simp2
    r19.21bi
    cB
    c0
    elsni
    syl
    #
    fveq2d
    @6
    @15
    cc0
    wceq
    #
    @13
    @0
    @2
    @17
    @5
    cS
    cM
    measvnul
    3ad2ant1
    #
    adantr
    eqtrd
    esumeq12dvaf
    @6
    @10
    @15
    cc0
    @6
    @9
    c0
    cM
    @6
    @9
    vx
    cA
    c0
    ciun
    c0
    @6
    vx
    cA
    cA
    cB
    c0
    @11
    measvunilem.0.1
    measvunilem.0.1
    @12
    @16
    iuneq12daf
    vx
    cA
    iun0
    syl6eq
    fveq2d
    @18
    eqtrd
    3eqtr4rd
end
