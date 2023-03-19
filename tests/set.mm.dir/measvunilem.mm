include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cesum.mm"
include "ciun.mm"
include "cpw.mm"
include "simp1.mm"
include "cvv.mm"
include "wss.mm"
include "simp3l.mm"
include "abrexctf.mm"
include "syl.mm"
include "ctex.mm"
include "simp2.mm"
include "eldifi.mm"
include "ralimi.mm"
include "nfcv.mm"
include "abrexss.mm"
include "elpwg.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "simp3r.mm"
include "disjabrexf.mm"
include "measvun.mm"
include "syl112anc.mm"
include "dfiun2g.mm"
include "fveq2d.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfbr.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "nf3an.mm"
include "fveq2.mm"
include "r19.21bi.mm"
include "disjdsct.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "simpl1.mm"
include "measvxrge0.mm"
include "sylan2.mm"
include "esumc.mm"
include "3eqtr4d.mm"

theorem measvunilem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  assume measvunilem.1: |- F/_ x A

  disjoint M x
  disjoint S x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint M y
  disjoint M z
  disjoint S y
  disjoint B y
  disjoint B z
  disjoint S z
  assert |- ( ( M e. ( measures ` S ) /\ A. x e. A B e. ( S \ { (/) } ) /\ ( A ~<_ _om /\ Disj_ x e. A B ) ) -> ( M ` U_ x e. A B ) = sum* x e. A ( M ` B ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cB
    cS
    c0
    csn
    #
    cdif
    #
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
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cuni
    #
    cM
    cfv
    #
    @9
    vz
    cv
    #
    cM
    cfv
    #
    vz
    cesum
    #
    vx
    cA
    cB
    ciun
    #
    cM
    cfv
    #
    cA
    cB
    cM
    cfv
    #
    vx
    cesum
    @8
    @0
    @9
    cS
    cpw
    wcel
    #
    @9
    com
    cdom
    wbr
    #
    vz
    @9
    @12
    wdisj
    #
    @11
    @14
    wceq
    @0
    @4
    @7
    simp1
    @8
    @9
    cvv
    wcel
    #
    @9
    cS
    wss
    #
    @18
    @8
    @19
    @21
    @8
    @5
    @19
    @0
    @4
    @5
    @6
    simp3l
    #
    vx
    vy
    cA
    cB
    measvunilem.1
    abrexctf
    syl
    #
    @9
    ctex
    syl
    @8
    @4
    @22
    @0
    @4
    @7
    simp2
    #
    @4
    cB
    cS
    wcel
    #
    vx
    cA
    wral
    @22
    @3
    @26
    vx
    cA
    cB
    cS
    @1
    eldifi
    #
    ralimi
    vx
    vy
    cA
    cB
    cS
    vx
    cS
    nfcv
    abrexss
    syl
    syl
    @21
    @18
    @22
    @9
    cS
    cvv
    elpwg
    biimpar
    syl2anc
    @24
    @8
    @6
    @20
    @0
    @4
    @5
    @6
    simp3r
    #
    vx
    vz
    vy
    cA
    cB
    measvunilem.1
    disjabrexf
    syl
    vz
    @9
    cS
    cM
    measvun
    syl112anc
    @8
    @4
    @16
    @11
    wceq
    @25
    @4
    @15
    @10
    cM
    vx
    vy
    cA
    cB
    @2
    dfiun2g
    fveq2d
    syl
    @8
    vz
    vy
    cA
    @17
    cB
    @13
    vx
    cvv
    @2
    vx
    @13
    nfcv
    @0
    @4
    @7
    vx
    @0
    vx
    nfv
    @3
    vx
    cA
    nfra1
    @5
    @6
    vx
    vx
    cA
    com
    cdom
    measvunilem.1
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
    measvunilem.1
    @12
    cB
    cM
    fveq2
    @8
    @5
    cA
    cvv
    wcel
    @23
    cA
    ctex
    syl
    @8
    vx
    cA
    cB
    cS
    @29
    measvunilem.1
    @8
    @3
    vx
    cA
    @25
    r19.21bi
    #
    @28
    disjdsct
    @8
    vx
    cv
    cA
    wcel
    #
    wa
    @0
    @3
    @17
    cc0
    cpnf
    cicc
    co
    wcel
    #
    @0
    @4
    @7
    @31
    simpl1
    @30
    @3
    @0
    @26
    @32
    @27
    cB
    cS
    cM
    measvxrge0
    sylan2
    syl2anc
    @30
    esumc
    3eqtr4d
end
