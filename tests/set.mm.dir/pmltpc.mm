include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wo.mm"
include "clt.mm"
include "w3a.mm"
include "wrex.mm"
include "w3o.mm"
include "wn.mm"
include "rexanali.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "weq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq1d.mm"
include "cbvral2v.mm"
include "xchbinx.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "ioran.mm"
include "3bitr4i.mm"
include "simplll.mm"
include "simpld.mm"
include "simprd.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "simprlr.mm"
include "simprrr.mm"
include "pmltpclem2.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "orrd.mm"
include "df-3or.mm"
include "sylibr.mm"

theorem pmltpc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vw: setvar w
  let vz: setvar z

  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F x
  disjoint F y
  disjoint a w
  disjoint a z
  disjoint b w
  disjoint b z
  disjoint c w
  disjoint c z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F w
  disjoint F z
  assert |- ( ( F e. ( RR ^pm RR ) /\ A C_ dom F ) -> ( A. x e. A A. y e. A ( x <_ y -> ( F ` x ) <_ ( F ` y ) ) \/ A. x e. A A. y e. A ( x <_ y -> ( F ` y ) <_ ( F ` x ) ) \/ E. a e. A E. b e. A E. c e. A ( a < b /\ b < c /\ ( ( ( F ` a ) < ( F ` b ) /\ ( F ` c ) < ( F ` b ) ) \/ ( ( F ` b ) < ( F ` a ) /\ ( F ` b ) < ( F ` c ) ) ) ) ) )

  proof
    cF
    cr
    cr
    cpm
    co
    wcel
    #
    cA
    cF
    cdm
    wss
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @3
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @5
    @7
    @6
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wo
    #
    va
    cv
    #
    vb
    cv
    #
    clt
    wbr
    @16
    vc
    cv
    #
    clt
    wbr
    @15
    cF
    cfv
    #
    @16
    cF
    cfv
    #
    clt
    wbr
    @17
    cF
    cfv
    #
    @19
    clt
    wbr
    wa
    @19
    @18
    clt
    wbr
    @19
    @20
    clt
    wbr
    wa
    wo
    w3a
    vc
    cA
    wrex
    vb
    cA
    wrex
    va
    cA
    wrex
    #
    wo
    @10
    @13
    @21
    w3o
    @2
    @14
    @21
    @14
    wn
    #
    @5
    @8
    wn
    #
    wa
    #
    vy
    cA
    wrex
    #
    vz
    cv
    #
    vw
    cv
    #
    cle
    wbr
    #
    @27
    cF
    cfv
    #
    @26
    cF
    cfv
    #
    cle
    wbr
    #
    wn
    #
    wa
    #
    vw
    cA
    wrex
    #
    wa
    #
    vz
    cA
    wrex
    vx
    cA
    wrex
    #
    @2
    @21
    @25
    vx
    cA
    wrex
    #
    @34
    vz
    cA
    wrex
    #
    wa
    @10
    wn
    #
    @13
    wn
    #
    wa
    @36
    @22
    @37
    @39
    @38
    @40
    @37
    @9
    wn
    #
    vx
    cA
    wrex
    @39
    @25
    @41
    vx
    cA
    @5
    @8
    vy
    cA
    rexanali
    rexbii
    @9
    vx
    cA
    rexnal
    bitri
    @38
    @28
    @31
    wi
    #
    vw
    cA
    wral
    #
    wn
    #
    vz
    cA
    wrex
    #
    @40
    @34
    @44
    vz
    cA
    @28
    @31
    vw
    cA
    rexanali
    rexbii
    @45
    @43
    vz
    cA
    wral
    @13
    @43
    vz
    cA
    rexnal
    @42
    @12
    @3
    @27
    cle
    wbr
    #
    @29
    @6
    cle
    wbr
    #
    wi
    vz
    vw
    vx
    vy
    cA
    cA
    vz
    vx
    weq
    #
    @28
    @46
    @31
    @47
    @26
    @3
    @27
    cle
    breq1
    @48
    @30
    @6
    @29
    cle
    @26
    @3
    cF
    fveq2
    breq2d
    imbi12d
    vw
    vy
    weq
    #
    @46
    @5
    @47
    @11
    @27
    @4
    @3
    cle
    breq2
    @49
    @29
    @7
    @6
    cle
    @27
    @4
    cF
    fveq2
    breq1d
    imbi12d
    cbvral2v
    xchbinx
    bitri
    anbi12i
    @25
    @34
    vx
    vz
    cA
    cA
    reeanv
    @10
    @13
    ioran
    3bitr4i
    @2
    @35
    @21
    vx
    vz
    cA
    cA
    @35
    @24
    @33
    wa
    #
    vw
    cA
    wrex
    vy
    cA
    wrex
    @2
    @3
    cA
    wcel
    #
    @26
    cA
    wcel
    #
    wa
    #
    wa
    #
    @21
    @24
    @33
    vy
    vw
    cA
    cA
    reeanv
    @54
    @50
    @21
    vy
    vw
    cA
    cA
    @54
    @4
    cA
    wcel
    #
    @27
    cA
    wcel
    #
    wa
    #
    wa
    #
    @50
    @21
    @58
    @50
    wa
    #
    cA
    @3
    cF
    @4
    @26
    @27
    va
    vb
    vc
    @59
    @0
    @1
    @2
    @53
    @57
    @50
    simplll
    #
    simpld
    @59
    @0
    @1
    @60
    simprd
    @59
    @51
    @52
    @2
    @53
    @57
    @50
    simpllr
    #
    simpld
    @54
    @55
    @56
    @50
    simplrl
    @59
    @51
    @52
    @61
    simprd
    @54
    @55
    @56
    @50
    simplrr
    @58
    @5
    @23
    @33
    simprll
    @58
    @24
    @28
    @32
    simprrl
    @58
    @5
    @23
    @33
    simprlr
    @58
    @24
    @28
    @32
    simprrr
    pmltpclem2
    ex
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    orrd
    @10
    @13
    @21
    df-3or
    sylibr
end
