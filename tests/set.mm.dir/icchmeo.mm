include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cii.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "ccn.mm"
include "ccnv.mm"
include "chmeo.mm"
include "cc0.mm"
include "c1.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "ctopon.mm"
include "cfv.mm"
include "iitopon.mm"
include "a1i.mm"
include "dfii3.mm"
include "oveq2i.mm"
include "ctop.mm"
include "wss.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "cnmptid.mm"
include "sseldi.mm"
include "cc.mm"
include "cnfldtopon.mm"
include "simp2.mm"
include "recnd.mm"
include "cnmptc.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "1cnd.mm"
include "subcn.mm"
include "simp1.mm"
include "addcn.mm"
include "syl5eqel.mm"
include "crn.mm"
include "wb.mm"
include "wf1o.mm"
include "wf.mm"
include "cdiv.mm"
include "wceq.mm"
include "iccf1o.mm"
include "simpld.mm"
include "f1of.mm"
include "frn.mm"
include "3syl.mm"
include "iccssre.mm"
include "3adant3.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "resttopon.mm"
include "sylancr.mm"
include "wne.mm"
include "crp.mm"
include "difrp.mm"
include "biimp3a.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divccn.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "cnmpt11.mm"
include "eqeltrd.mm"
include "cdm.mm"
include "dfdm4.mm"
include "eqimss2i.mm"
include "f1odm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "unitssre.mm"
include "syl6eleqr.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem icchmeo
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let vy: setvar y
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  assume icchmeo.j: |- J = ( TopOpen ` CCfld )
  assume icchmeo.f: |- F = ( x e. ( 0 [,] 1 ) |-> ( ( x x. B ) + ( ( 1 - x ) x. A ) ) )

  disjoint A x
  disjoint B x
  disjoint J x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint v x
  disjoint J v
  disjoint w x
  disjoint J w
  disjoint x z
  disjoint J y
  disjoint J z
  assert |- ( ( A e. RR /\ B e. RR /\ A < B ) -> F e. ( II Homeo ( J |`t ( A [,] B ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cF
    cii
    cJ
    cA
    cB
    cicc
    co
    #
    crest
    co
    #
    ccn
    co
    wcel
    #
    cF
    ccnv
    #
    @5
    cii
    ccn
    co
    #
    wcel
    cF
    cii
    @5
    chmeo
    co
    wcel
    @3
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @6
    @3
    cF
    vx
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    cB
    cmul
    co
    #
    c1
    @12
    cmin
    co
    #
    cA
    cmul
    co
    #
    caddc
    co
    cmpt
    @9
    icchmeo.f
    @3
    vx
    @13
    @15
    caddc
    cii
    cJ
    cJ
    cJ
    @11
    cii
    @11
    ctopon
    cfv
    wcel
    @3
    iitopon
    a1i
    #
    @3
    vx
    @12
    cB
    cmul
    cii
    cJ
    cJ
    cJ
    @11
    @16
    @3
    cii
    cii
    ccn
    co
    #
    @9
    vx
    @11
    @12
    cmpt
    @17
    cii
    cJ
    @11
    crest
    co
    #
    ccn
    co
    #
    @9
    cii
    @18
    cii
    ccn
    cJ
    icchmeo.j
    dfii3
    #
    oveq2i
    cJ
    ctop
    wcel
    #
    @19
    @9
    wss
    cJ
    icchmeo.j
    cnfldtop
    #
    @11
    cii
    cJ
    cnrest2r
    ax-mp
    eqsstri
    @3
    vx
    cii
    @11
    @16
    cnmptid
    sseldi
    #
    @3
    vx
    cB
    cii
    cJ
    @11
    cc
    @16
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    @3
    cJ
    icchmeo.j
    cnfldtopon
    #
    a1i
    #
    @3
    cB
    @0
    @1
    @2
    simp2
    recnd
    cnmptc
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    #
    wcel
    @3
    cJ
    icchmeo.j
    mulcn
    a1i
    #
    cnmpt12f
    @3
    vx
    @14
    cA
    cmul
    cii
    cJ
    cJ
    cJ
    @11
    @16
    @3
    vx
    c1
    @12
    cmin
    cii
    cJ
    cJ
    cJ
    @11
    @16
    @3
    vx
    c1
    cii
    cJ
    @11
    cc
    @16
    @26
    @3
    1cnd
    cnmptc
    @23
    cmin
    @27
    wcel
    @3
    cJ
    icchmeo.j
    subcn
    a1i
    #
    cnmpt12f
    @3
    vx
    cA
    cii
    cJ
    @11
    cc
    @16
    @26
    @3
    cA
    @0
    @1
    @2
    simp1
    recnd
    #
    cnmptc
    @28
    cnmpt12f
    caddc
    @27
    wcel
    @3
    cJ
    icchmeo.j
    addcn
    a1i
    cnmpt12f
    syl5eqel
    @3
    @24
    cF
    crn
    @4
    wss
    #
    @4
    cc
    wss
    #
    @10
    @6
    wb
    @26
    @3
    @11
    @4
    cF
    wf1o
    #
    @11
    @4
    cF
    wf
    @31
    @3
    @33
    @7
    vy
    @4
    vy
    cv
    #
    cA
    cmin
    co
    #
    cB
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    vx
    vy
    cA
    cB
    cF
    icchmeo.f
    iccf1o
    #
    simpld
    #
    @11
    @4
    cF
    f1of
    @11
    @4
    cF
    frn
    3syl
    @3
    @4
    cr
    cc
    @0
    @1
    @4
    cr
    wss
    @2
    cA
    cB
    iccssre
    3adant3
    ax-resscn
    syl6ss
    #
    @4
    cF
    cii
    cJ
    cc
    cnrest2
    syl3anc
    mpbid
    @3
    @7
    @5
    @18
    ccn
    co
    #
    @8
    @3
    @7
    @5
    cJ
    ccn
    co
    #
    wcel
    #
    @7
    @43
    wcel
    #
    @3
    @7
    @38
    @44
    @3
    @33
    @39
    @40
    simprd
    @3
    vy
    vx
    @35
    @12
    @36
    cdiv
    co
    #
    @37
    @5
    cJ
    cJ
    @4
    cc
    @3
    @24
    @32
    @5
    @4
    ctopon
    cfv
    wcel
    @25
    @42
    @4
    cJ
    cc
    resttopon
    sylancr
    #
    @3
    vy
    @34
    cA
    cmin
    @5
    cJ
    cJ
    cJ
    @4
    @48
    @3
    @5
    @5
    ccn
    co
    #
    @44
    vy
    @4
    @34
    cmpt
    @21
    @49
    @44
    wss
    @22
    @4
    @5
    cJ
    cnrest2r
    ax-mp
    @3
    vy
    @5
    @4
    @48
    cnmptid
    sseldi
    @3
    vy
    cA
    @5
    cJ
    @4
    cc
    @48
    @26
    @30
    cnmptc
    @29
    cnmpt12f
    @26
    @3
    @36
    cc
    wcel
    @36
    cc0
    wne
    vx
    cc
    @47
    cmpt
    cJ
    cJ
    ccn
    co
    wcel
    @3
    @36
    @0
    @1
    @2
    @36
    crp
    wcel
    cA
    cB
    difrp
    biimp3a
    #
    rpcnd
    @3
    @36
    @50
    rpne0d
    vx
    @36
    cJ
    icchmeo.j
    divccn
    syl2anc
    @12
    @35
    @36
    cdiv
    oveq1
    cnmpt11
    eqeltrd
    @3
    @24
    @7
    crn
    #
    @11
    wss
    @11
    cc
    wss
    @45
    @46
    wb
    @26
    @3
    cF
    cdm
    #
    @51
    @11
    @52
    @51
    cF
    dfdm4
    eqimss2i
    @3
    @33
    @52
    @11
    wceq
    @41
    @11
    @4
    cF
    f1odm
    syl
    syl5sseq
    @3
    @11
    cr
    cc
    @11
    cr
    wss
    @3
    unitssre
    a1i
    ax-resscn
    syl6ss
    @11
    @7
    @5
    cJ
    cc
    cnrest2
    syl3anc
    mpbid
    cii
    @18
    @5
    ccn
    @20
    oveq2i
    syl6eleqr
    cF
    cii
    @5
    ishmeo
    sylanbrc
end
