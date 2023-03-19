include "wfun.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "nfv.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcxfr.mm"
include "nffun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "fveq2.mm"
include "wbr.mm"
include "simplr.mm"
include "fliftel1.mm"
include "ad2ant2r.mm"
include "funbrfv.mm"
include "sylc.mm"
include "wrex.mm"
include "simprr.mm"
include "eqidd.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "fliftel.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "exp31.mm"
include "ralrimd.mm"
include "wal.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "reeanv.mm"
include "r19.29.mm"
include "eqtr2.mm"
include "imim1i.mm"
include "imp.mm"
include "simprlr.mm"
include "simprrr.mm"
include "3eqtr4d.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "syl5bir.mm"
include "syl9.mm"
include "alrimdv.mm"
include "wrel.mm"
include "cxp.mm"
include "wss.mm"
include "fliftrel.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "dffun2.mm"
include "baib.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem fliftfun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cY: class Y
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )
  assume fliftfun.4: |- ( x = y -> A = C )
  assume fliftfun.5: |- ( x = y -> B = D )

  disjoint A y
  disjoint B y
  disjoint C x
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint D x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint S x
  disjoint S y
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint x z
  disjoint C z
  disjoint R z
  disjoint Y x
  disjoint D u
  disjoint D v
  disjoint D z
  disjoint F u
  disjoint F v
  disjoint F z
  disjoint ph u
  disjoint ph v
  disjoint ph z
  disjoint X u
  disjoint X v
  disjoint X z
  disjoint S z
  assert |- ( ph -> ( Fun F <-> A. x e. X A. y e. X ( A = C -> B = D ) ) )

  proof
    wph
    cF
    wfun
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wph
    @0
    @4
    vx
    cX
    wph
    vx
    nfv
    vx
    cF
    vx
    cF
    vx
    cX
    cA
    cB
    cop
    #
    cmpt
    #
    crn
    flift.1
    vx
    @7
    vx
    cX
    @6
    nfmpt1
    nfrn
    nfcxfr
    nffun
    wph
    @0
    vx
    cv
    #
    cX
    wcel
    #
    @4
    wph
    @0
    wa
    #
    @9
    wa
    @3
    vy
    cX
    @10
    @9
    vy
    cv
    #
    cX
    wcel
    #
    @3
    @1
    cA
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    wceq
    @10
    @9
    @12
    wa
    #
    wa
    #
    @2
    cA
    cC
    cF
    fveq2
    @16
    @13
    cB
    @14
    cD
    @16
    @0
    cA
    cB
    cF
    wbr
    #
    @13
    cB
    wceq
    wph
    @0
    @15
    simplr
    #
    wph
    @9
    @17
    @0
    @12
    wph
    vx
    cA
    cB
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel1
    ad2ant2r
    cA
    cB
    cF
    funbrfv
    sylc
    @16
    @0
    cC
    cD
    cF
    wbr
    #
    @14
    cD
    wceq
    @18
    @16
    @19
    cC
    cA
    wceq
    #
    cD
    cB
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    @16
    @12
    cC
    cC
    wceq
    #
    cD
    cD
    wceq
    #
    @23
    @10
    @9
    @12
    simprr
    @16
    cC
    eqidd
    @16
    cD
    eqidd
    @22
    @24
    @25
    wa
    vx
    @11
    cX
    @8
    @11
    wceq
    #
    @20
    @24
    @21
    @25
    @26
    cA
    cC
    cC
    fliftfun.4
    eqeq2d
    @26
    cB
    cD
    cD
    fliftfun.5
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    wph
    @19
    @23
    wb
    @0
    @15
    wph
    vx
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel
    ad2antrr
    mpbird
    cC
    cD
    cF
    funbrfv
    sylc
    eqeq12d
    syl5ib
    anassrs
    ralrimiva
    exp31
    ralrimd
    wph
    @5
    vz
    cv
    #
    vu
    cv
    #
    cF
    wbr
    #
    @27
    vv
    cv
    #
    cF
    wbr
    #
    wa
    #
    @28
    @30
    wceq
    #
    wi
    #
    vv
    wal
    #
    vu
    wal
    #
    vz
    wal
    #
    @0
    wph
    @5
    @36
    vz
    wph
    @5
    @35
    vu
    wph
    @5
    @34
    vv
    wph
    @32
    @27
    cA
    wceq
    #
    @28
    cB
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    @27
    cC
    wceq
    #
    @30
    cD
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    wa
    #
    @5
    @33
    wph
    @32
    @46
    wph
    @29
    @41
    @31
    @45
    wph
    vx
    cA
    cB
    @27
    @28
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel
    wph
    @31
    @38
    @30
    cB
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    @45
    wph
    vx
    cA
    cB
    @27
    @30
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel
    @48
    @44
    vx
    vy
    cX
    @26
    @38
    @42
    @47
    @43
    @26
    cA
    cC
    @27
    fliftfun.4
    eqeq2d
    @26
    cB
    cD
    @30
    fliftfun.5
    eqeq2d
    anbi12d
    cbvrexv
    syl6bb
    anbi12d
    biimpd
    @46
    @40
    @44
    wa
    #
    vy
    cX
    wrex
    #
    vx
    cX
    wrex
    #
    @5
    @33
    @40
    @44
    vx
    vy
    cX
    cX
    reeanv
    @5
    @51
    @33
    @5
    @51
    wa
    @4
    @50
    wa
    #
    vx
    cX
    wrex
    @33
    @4
    @50
    vx
    cX
    r19.29
    @52
    @33
    vx
    cX
    @52
    @3
    @49
    wa
    #
    vy
    cX
    wrex
    @33
    @3
    @49
    vy
    cX
    r19.29
    @53
    @33
    vy
    cX
    @53
    cB
    cD
    @28
    @30
    @3
    @49
    @2
    @49
    @1
    @2
    @38
    @42
    @1
    @39
    @43
    @27
    cA
    cC
    eqtr2
    ad2ant2r
    imim1i
    imp
    @3
    @38
    @39
    @44
    simprlr
    @3
    @40
    @42
    @43
    simprrr
    3eqtr4d
    rexlimivw
    syl
    rexlimivw
    syl
    ex
    syl5bir
    syl9
    alrimdv
    alrimdv
    alrimdv
    wph
    cF
    wrel
    #
    @0
    @37
    wb
    wph
    cF
    cR
    cS
    cxp
    #
    wss
    @55
    wrel
    @54
    wph
    vx
    cA
    cB
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftrel
    cR
    cS
    relxp
    cF
    @55
    relss
    mpisyl
    @0
    @54
    @37
    vz
    vu
    vv
    cF
    dffun2
    baib
    syl
    sylibrd
    impbid
end
