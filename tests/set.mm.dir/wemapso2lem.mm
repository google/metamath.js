include "wcel.mm"
include "wor.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cvv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "wne.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "csupp.mm"
include "cun.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "simprll.mm"
include "breq1.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "simprlr.mm"
include "fsuppunfi.mm"
include "cfv.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "sseldi.mm"
include "elmapi.mm"
include "ffn.mm"
include "fndmdif.mm"
include "syl2anc.mm"
include "wi.mm"
include "wo.mm"
include "eqtr3.mm"
include "necon3ai.mm"
include "neorian.mm"
include "sylibr.mm"
include "elun.mm"
include "csn.mm"
include "wb.mm"
include "fvex.mm"
include "eldifsn.mm"
include "mpbiran.mm"
include "bicomi.mm"
include "a1i.mm"
include "anbi2d.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "syl6bb.mm"
include "simpll1.mm"
include "orbi12d.mm"
include "syl5bb.mm"
include "syl5ibr.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "eqsstrd.mm"
include "ssfi.mm"
include "wwe.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "unssd.mm"
include "soss.mm"
include "sylc.mm"
include "wofi.mm"
include "wefr.mm"
include "simprr.mm"
include "fndmdifeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "fri.mm"
include "syl22anc.mm"
include "wemapsolem.mm"

theorem wemapso2lem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cX: class X
  let cP: class P
  let cQ: class Q
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }
  assume wemapso2.u: |- U = { x e. ( B ^m A ) | x finSupp Z }

  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Z x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W d
  disjoint Z a
  disjoint Z b
  assert |- ( ( ( A e. V /\ R Or A /\ S Or B ) /\ Z e. W ) -> T Or U )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    wor
    #
    cB
    cS
    wor
    #
    w3a
    #
    cZ
    cW
    wcel
    #
    wa
    #
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    cS
    cT
    cU
    va
    vb
    vc
    vd
    wemapso.t
    cU
    vx
    cv
    #
    cZ
    cfsupp
    wbr
    #
    vx
    cB
    cA
    cmap
    co
    #
    crab
    @8
    wemapso2.u
    @7
    vx
    @8
    ssrab2
    eqsstri
    #
    @3
    cA
    cvv
    wcel
    #
    @4
    @0
    @1
    @10
    @2
    cA
    cV
    elex
    3ad2ant1
    adantr
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    @0
    @1
    @2
    @4
    simpl3
    @5
    va
    cv
    #
    cU
    wcel
    #
    vb
    cv
    #
    cU
    wcel
    #
    wa
    #
    @13
    @15
    wne
    #
    wa
    #
    wa
    #
    @13
    @15
    cdif
    cdm
    #
    cfn
    wcel
    #
    @13
    cZ
    csupp
    co
    #
    @15
    cZ
    csupp
    co
    #
    cun
    #
    cR
    wfr
    #
    @21
    @25
    wss
    #
    @21
    c0
    wne
    #
    vd
    cv
    vc
    cv
    #
    cR
    wbr
    wn
    vd
    @21
    wral
    vc
    @21
    wrex
    @20
    @25
    cfn
    wcel
    #
    @27
    @22
    @20
    @13
    @15
    cZ
    @20
    @14
    @13
    cZ
    cfsupp
    wbr
    #
    @5
    @14
    @16
    @18
    simprll
    #
    @14
    @13
    @8
    wcel
    #
    @31
    @7
    @31
    vx
    @13
    @8
    cU
    @6
    @13
    cZ
    cfsupp
    breq1
    wemapso2.u
    elrab2
    simprbi
    syl
    @20
    @16
    @15
    cZ
    cfsupp
    wbr
    #
    @5
    @14
    @16
    @18
    simprlr
    #
    @16
    @15
    @8
    wcel
    #
    @34
    @7
    @34
    vx
    @15
    @8
    cU
    @6
    @15
    cZ
    cfsupp
    breq1
    wemapso2.u
    elrab2
    simprbi
    syl
    fsuppunfi
    #
    @20
    @21
    @29
    @13
    cfv
    #
    @29
    @15
    cfv
    #
    wne
    #
    vc
    cA
    crab
    #
    @25
    @20
    @13
    cA
    wfn
    #
    @15
    cA
    wfn
    #
    @21
    @41
    wceq
    @20
    cA
    cB
    @13
    wf
    #
    @42
    @20
    @33
    @44
    @20
    cU
    @8
    @13
    @9
    @32
    sseldi
    @13
    cB
    cA
    elmapi
    syl
    #
    cA
    cB
    @13
    ffn
    syl
    #
    @20
    cA
    cB
    @15
    wf
    #
    @43
    @20
    @36
    @47
    @20
    cU
    @8
    @15
    @9
    @35
    sseldi
    @15
    cB
    cA
    elmapi
    syl
    #
    cA
    cB
    @15
    ffn
    syl
    #
    vc
    cA
    @13
    @15
    fndmdif
    syl2anc
    @20
    @40
    @29
    @25
    wcel
    #
    wi
    #
    vc
    cA
    wral
    @41
    @25
    wss
    @20
    @51
    vc
    cA
    @40
    @50
    @20
    @29
    cA
    wcel
    #
    wa
    #
    @38
    cZ
    wne
    #
    @39
    cZ
    wne
    #
    wo
    #
    @40
    @38
    cZ
    wceq
    @39
    cZ
    wceq
    wa
    #
    wn
    @56
    @57
    @38
    @39
    @38
    @39
    cZ
    eqtr3
    necon3ai
    @38
    cZ
    @39
    cZ
    neorian
    sylibr
    @50
    @29
    @23
    wcel
    #
    @29
    @24
    wcel
    #
    wo
    @53
    @56
    @29
    @23
    @24
    elun
    @53
    @58
    @54
    @59
    @55
    @53
    @58
    @38
    cvv
    cZ
    csn
    cdif
    #
    wcel
    #
    @54
    @53
    @52
    @54
    wa
    #
    @52
    @61
    wa
    @58
    @61
    @53
    @54
    @61
    @52
    @54
    @61
    wb
    @53
    @61
    @54
    @61
    @38
    cvv
    wcel
    @54
    @29
    @13
    fvex
    @38
    cvv
    cZ
    eldifsn
    mpbiran
    #
    bicomi
    a1i
    anbi2d
    @53
    @42
    @10
    @4
    @58
    @62
    wb
    @20
    @42
    @52
    @46
    adantr
    @5
    @10
    @19
    @52
    @11
    ad2antrr
    @5
    @4
    @19
    @52
    @3
    @4
    simpr
    ad2antrr
    #
    @29
    @13
    cvv
    cW
    cA
    cZ
    elsuppfn
    syl3anc
    @53
    @52
    @61
    @20
    @52
    simpr
    #
    biantrurd
    3bitr4d
    @63
    syl6bb
    @53
    @59
    @39
    @60
    wcel
    #
    @55
    @53
    @52
    @55
    wa
    #
    @52
    @66
    wa
    @59
    @66
    @53
    @55
    @66
    @52
    @55
    @66
    wb
    @53
    @66
    @55
    @66
    @39
    cvv
    wcel
    @55
    @29
    @15
    fvex
    @39
    cvv
    cZ
    eldifsn
    mpbiran
    #
    bicomi
    a1i
    anbi2d
    @53
    @43
    @0
    @4
    @59
    @67
    wb
    @20
    @43
    @52
    @49
    adantr
    @20
    @0
    @52
    @0
    @1
    @2
    @4
    @19
    simpll1
    adantr
    @64
    @29
    @15
    cV
    cW
    cA
    cZ
    elsuppfn
    syl3anc
    @53
    @52
    @66
    @65
    biantrurd
    3bitr4d
    @68
    syl6bb
    orbi12d
    syl5bb
    syl5ibr
    ralrimiva
    @40
    vc
    cA
    @25
    rabss
    sylibr
    eqsstrd
    #
    @25
    @21
    ssfi
    syl2anc
    @20
    @25
    cR
    wwe
    #
    @26
    @20
    @25
    cR
    wor
    #
    @30
    @70
    @20
    @25
    cA
    wss
    @1
    @71
    @20
    @23
    @24
    cA
    @20
    @13
    cdm
    #
    @23
    cA
    @13
    cZ
    suppssdm
    @20
    @44
    @72
    cA
    wceq
    @45
    cA
    cB
    @13
    fdm
    syl
    syl5sseq
    @20
    @15
    cdm
    #
    @24
    cA
    @15
    cZ
    suppssdm
    @20
    @47
    @73
    cA
    wceq
    @48
    cA
    cB
    @15
    fdm
    syl
    syl5sseq
    unssd
    @5
    @1
    @19
    @12
    adantr
    @25
    cA
    cR
    soss
    sylc
    @37
    @25
    cR
    wofi
    syl2anc
    @25
    cR
    wefr
    syl
    @69
    @20
    @28
    @18
    @5
    @17
    @18
    simprr
    @20
    @21
    c0
    @13
    @15
    @20
    @42
    @43
    @21
    c0
    wceq
    @13
    @15
    wceq
    wb
    @46
    @49
    cA
    @13
    @15
    fndmdifeq0
    syl2anc
    necon3bid
    mpbird
    vc
    vd
    @25
    @21
    cfn
    cR
    fri
    syl22anc
    wemapsolem
end
