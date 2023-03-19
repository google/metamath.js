include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "elznn0nn.mm"
include "wi.mm"
include "expcllem.mm"
include "ex.mm"
include "adantr.mm"
include "c1.mm"
include "cdiv.mm"
include "cc.mm"
include "wceq.mm"
include "simpll.mm"
include "sseldi.mm"
include "simprl.mm"
include "recnd.mm"
include "nnnn0.mm"
include "ad2antll.mm"
include "expneg2.mm"
include "syl3anc.mm"
include "csn.mm"
include "cdif.mm"
include "difss.mm"
include "simpl.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "sstri.mm"
include "cv.mm"
include "cmul.mm"
include "sseli.mm"
include "syl2an.mm"
include "anim1i.mm"
include "sylbi.mm"
include "mulne0.mm"
include "sylanbrc.mm"
include "ax-1ne0.mm"
include "mpbir2an.mm"
include "syl2anc.mm"
include "sylib.mm"
include "simprd.mm"
include "neeq1.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclga.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "jaod.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem expcl2lem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  let vw: setvar w
  assume expcllem.1: |- F C_ CC
  assume expcllem.2: |- ( ( x e. F /\ y e. F ) -> ( x x. y ) e. F )
  assume expcllem.3: |- 1 e. F
  assume expcl2lem.4: |- ( ( x e. F /\ x =/= 0 ) -> ( 1 / x ) e. F )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint F z
  disjoint F w
  assert |- ( ( A e. F /\ A =/= 0 /\ B e. ZZ ) -> ( A ^ B ) e. F )

  proof
    cA
    cF
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cexp
    co
    #
    cF
    wcel
    #
    @2
    cB
    cn0
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    @0
    @1
    wa
    #
    @4
    cB
    elznn0nn
    @10
    @5
    @4
    @9
    @0
    @5
    @4
    wi
    @1
    @0
    @5
    @4
    vx
    vy
    cA
    cB
    cF
    expcllem.1
    expcllem.2
    expcllem.3
    expcllem
    ex
    adantr
    @10
    @9
    @4
    @10
    @9
    wa
    #
    @3
    c1
    cA
    @7
    cexp
    co
    #
    cdiv
    co
    #
    cF
    @11
    cA
    cc
    wcel
    cB
    cc
    wcel
    @7
    cn0
    wcel
    #
    @3
    @13
    wceq
    @11
    cF
    cc
    cA
    expcllem.1
    @0
    @1
    @9
    simpll
    sseldi
    @11
    cB
    @10
    @6
    @8
    simprl
    recnd
    @8
    @14
    @10
    @6
    @7
    nnnn0
    ad2antll
    #
    cA
    cB
    expneg2
    syl3anc
    @11
    @12
    cF
    wcel
    #
    @12
    cc0
    wne
    #
    @13
    cF
    wcel
    #
    @11
    cF
    cc0
    csn
    #
    cdif
    #
    cF
    @12
    cF
    @19
    difss
    #
    @11
    cA
    @20
    wcel
    #
    @14
    @12
    @20
    wcel
    #
    @11
    @10
    @22
    @10
    @9
    simpl
    cA
    cF
    cc0
    eldifsn
    sylibr
    @15
    vx
    vy
    cA
    @7
    @20
    @20
    cF
    cc
    @21
    expcllem.1
    sstri
    vx
    cv
    #
    @20
    wcel
    #
    vy
    cv
    #
    @20
    wcel
    #
    wa
    @24
    @26
    cmul
    co
    #
    cF
    wcel
    #
    @28
    cc0
    wne
    #
    @28
    @20
    wcel
    @25
    @24
    cF
    wcel
    #
    @26
    cF
    wcel
    #
    @29
    @27
    @20
    cF
    @24
    @21
    sseli
    @20
    cF
    @26
    @21
    sseli
    expcllem.2
    syl2an
    @25
    @24
    cc
    wcel
    #
    @24
    cc0
    wne
    #
    wa
    #
    @26
    cc
    wcel
    #
    @26
    cc0
    wne
    #
    wa
    #
    @30
    @27
    @25
    @31
    @34
    wa
    @35
    @24
    cF
    cc0
    eldifsn
    @31
    @33
    @34
    cF
    cc
    @24
    expcllem.1
    sseli
    anim1i
    sylbi
    @27
    @32
    @37
    wa
    @38
    @26
    cF
    cc0
    eldifsn
    @32
    @36
    @37
    cF
    cc
    @26
    expcllem.1
    sseli
    anim1i
    sylbi
    @24
    @26
    mulne0
    syl2an
    @28
    cF
    cc0
    eldifsn
    sylanbrc
    c1
    @20
    wcel
    c1
    cF
    wcel
    c1
    cc0
    wne
    expcllem.3
    ax-1ne0
    c1
    cF
    cc0
    eldifsn
    mpbir2an
    expcllem
    syl2anc
    #
    sseldi
    @11
    @16
    @17
    @11
    @23
    @16
    @17
    wa
    @39
    @12
    cF
    cc0
    eldifsn
    sylib
    simprd
    @34
    c1
    @24
    cdiv
    co
    #
    cF
    wcel
    #
    wi
    @17
    @18
    wi
    vx
    @12
    cF
    @24
    @12
    wceq
    #
    @34
    @17
    @41
    @18
    @24
    @12
    cc0
    neeq1
    @42
    @40
    @13
    cF
    @24
    @12
    c1
    cdiv
    oveq2
    eleq1d
    imbi12d
    @31
    @34
    @41
    expcl2lem.4
    ex
    vtoclga
    sylc
    eqeltrd
    ex
    jaod
    syl5bi
    3impia
end
