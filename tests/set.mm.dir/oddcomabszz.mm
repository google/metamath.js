include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "csb.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "chvar.mm"
include "adantr.mm"
include "w3a.mm"
include "nfcv.mm"
include "nfbr.mm"
include "breq2.mm"
include "3anbi23d.mm"
include "breq2d.mm"
include "3expa.mm"
include "absidd.mm"
include "zre.mm"
include "ad2antlr.mm"
include "absid.mm"
include "sylancom.mm"
include "eqtr4d.mm"
include "cneg.mm"
include "negex.mm"
include "csbie.mm"
include "negeq.mm"
include "syl5eqr.mm"
include "vex.mm"
include "negeqd.mm"
include "absnid.mm"
include "znegcl.mm"
include "vtoclf.mm"
include "3expia.mm"
include "sylan2.mm"
include "sylibd.mm"
include "adantl.mm"
include "le0neg1d.mm"
include "3imtr4d.mm"
include "imp.mm"
include "absnidd.mm"
include "3eqtr4rd.mm"
include "wo.mm"
include "0re.mm"
include "letric.mm"
include "sylancr.mm"
include "mpjaodan.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "fvex.mm"
include "a1i.mm"
include "3eqtr3d.mm"

theorem oddcomabszz
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let va: setvar a
  assume oddcomabszz.1: |- ( ( ph /\ x e. ZZ ) -> A e. RR )
  assume oddcomabszz.2: |- ( ( ph /\ x e. ZZ /\ 0 <_ x ) -> 0 <_ A )
  assume oddcomabszz.3: |- ( ( ph /\ y e. ZZ ) -> C = -u B )
  assume oddcomabszz.4: |- ( x = y -> A = B )
  assume oddcomabszz.5: |- ( x = -u y -> A = C )
  assume oddcomabszz.6: |- ( x = D -> A = E )
  assume oddcomabszz.7: |- ( x = ( abs ` D ) -> A = F )

  disjoint B x
  disjoint C x
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint E x
  disjoint F x
  disjoint A y
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint a x
  disjoint C a
  disjoint D a
  disjoint a y
  disjoint E a
  disjoint F a
  disjoint A a
  disjoint a ph
  assert |- ( ( ph /\ D e. ZZ ) -> ( abs ` E ) = F )

  proof
    wph
    cD
    cz
    wcel
    #
    wa
    #
    vx
    cD
    cA
    csb
    #
    cabs
    cfv
    #
    vx
    cD
    cabs
    cfv
    #
    cA
    csb
    #
    cE
    cabs
    cfv
    #
    cF
    wph
    @0
    @3
    @5
    wceq
    #
    wph
    va
    cv
    #
    cz
    wcel
    #
    wa
    #
    vx
    @8
    cA
    csb
    #
    cabs
    cfv
    #
    vx
    @8
    cabs
    cfv
    #
    cA
    csb
    #
    wceq
    #
    wi
    @1
    @7
    wi
    va
    cD
    cz
    @8
    cD
    wceq
    #
    @10
    @1
    @15
    @7
    @16
    @9
    @0
    wph
    @8
    cD
    cz
    eleq1
    anbi2d
    @16
    @12
    @3
    @14
    @5
    @16
    @11
    @2
    cabs
    vx
    @8
    cD
    cA
    csbeq1
    fveq2d
    @16
    vx
    @13
    @4
    cA
    @8
    cD
    cabs
    fveq2
    csbeq1d
    eqeq12d
    imbi12d
    @10
    cc0
    @8
    cle
    wbr
    #
    @15
    @8
    cc0
    cle
    wbr
    #
    @10
    @17
    wa
    #
    @12
    @11
    @14
    @19
    @11
    @10
    @11
    cr
    wcel
    #
    @17
    wph
    vx
    cv
    #
    cz
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    #
    wi
    @10
    @20
    wi
    vx
    va
    @10
    @20
    vx
    @10
    vx
    nfv
    vx
    @11
    cr
    vx
    @8
    cA
    nfcsb1v
    #
    nfel1
    nfim
    @21
    @8
    wceq
    #
    @23
    @10
    @24
    @20
    @26
    @22
    @9
    wph
    @21
    @8
    cz
    eleq1
    #
    anbi2d
    @26
    cA
    @11
    cr
    vx
    @8
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    oddcomabszz.1
    chvar
    #
    adantr
    wph
    @9
    @17
    cc0
    @11
    cle
    wbr
    #
    wph
    @22
    cc0
    @21
    cle
    wbr
    #
    w3a
    #
    cc0
    cA
    cle
    wbr
    #
    wi
    #
    wph
    @9
    @17
    w3a
    #
    @30
    wi
    vx
    va
    @35
    @30
    vx
    @35
    vx
    nfv
    vx
    cc0
    @11
    cle
    vx
    cc0
    nfcv
    #
    vx
    cle
    nfcv
    #
    @25
    nfbr
    nfim
    @26
    @32
    @35
    @33
    @30
    @26
    @22
    @9
    @31
    @17
    wph
    @27
    @21
    @8
    cc0
    cle
    breq2
    3anbi23d
    @26
    cA
    @11
    cc0
    cle
    @28
    breq2d
    imbi12d
    oddcomabszz.2
    chvar
    3expa
    absidd
    @19
    vx
    @13
    @8
    cA
    @10
    @17
    @8
    cr
    wcel
    #
    @13
    @8
    wceq
    @9
    @38
    wph
    @17
    @8
    zre
    #
    ad2antlr
    @8
    absid
    sylancom
    csbeq1d
    eqtr4d
    @10
    @18
    wa
    #
    vx
    @8
    cneg
    #
    cA
    csb
    #
    @11
    cneg
    #
    @14
    @12
    @10
    @42
    @43
    wceq
    #
    @18
    wph
    vy
    cv
    #
    cz
    wcel
    #
    wa
    #
    cC
    cB
    cneg
    #
    wceq
    #
    wi
    @10
    @44
    wi
    #
    vy
    va
    @50
    vy
    nfv
    @45
    @8
    wceq
    #
    @47
    @10
    @49
    @44
    @51
    @46
    @9
    wph
    @45
    @8
    cz
    eleq1
    anbi2d
    @51
    cC
    @42
    @48
    @43
    @51
    cC
    vx
    @45
    cneg
    #
    cA
    csb
    @42
    vx
    @52
    cA
    cC
    @45
    negex
    oddcomabszz.5
    csbie
    @51
    vx
    @52
    @41
    cA
    @45
    @8
    negeq
    csbeq1d
    syl5eqr
    @51
    cB
    @11
    @51
    cB
    vx
    @45
    cA
    csb
    @11
    vx
    @45
    cA
    cB
    vy
    vex
    oddcomabszz.4
    csbie
    vx
    @45
    @8
    cA
    csbeq1
    syl5eqr
    negeqd
    eqeq12d
    imbi12d
    oddcomabszz.3
    chvar
    #
    adantr
    @40
    vx
    @13
    @41
    cA
    @10
    @18
    @38
    @13
    @41
    wceq
    @9
    @38
    wph
    @18
    @39
    ad2antlr
    @8
    absnid
    sylancom
    csbeq1d
    @40
    @11
    @10
    @20
    @18
    @29
    adantr
    @10
    @18
    @11
    cc0
    cle
    wbr
    #
    @10
    cc0
    @41
    cle
    wbr
    #
    cc0
    @43
    cle
    wbr
    #
    @18
    @54
    @10
    @55
    cc0
    @42
    cle
    wbr
    #
    @56
    @9
    wph
    @41
    cz
    wcel
    #
    @55
    @57
    wi
    @8
    znegcl
    wph
    @58
    @55
    @57
    @34
    wph
    @58
    @55
    w3a
    #
    @57
    wi
    vx
    @41
    @59
    @57
    vx
    @59
    vx
    nfv
    vx
    cc0
    @42
    cle
    @36
    @37
    vx
    @41
    cA
    nfcsb1v
    nfbr
    nfim
    @8
    negex
    @21
    @41
    wceq
    #
    @32
    @59
    @33
    @57
    @60
    @22
    @58
    @31
    @55
    wph
    @21
    @41
    cz
    eleq1
    @21
    @41
    cc0
    cle
    breq2
    3anbi23d
    @60
    cA
    @42
    cc0
    cle
    vx
    @41
    cA
    csbeq1a
    breq2d
    imbi12d
    oddcomabszz.2
    vtoclf
    3expia
    sylan2
    @10
    @42
    @43
    cc0
    cle
    @53
    breq2d
    sylibd
    @10
    @8
    @9
    @38
    wph
    @39
    adantl
    le0neg1d
    @10
    @11
    @29
    le0neg1d
    3imtr4d
    imp
    absnidd
    3eqtr4rd
    @9
    @17
    @18
    wo
    #
    wph
    @9
    cc0
    cr
    wcel
    @38
    @61
    0re
    @39
    cc0
    @8
    letric
    sylancr
    adantl
    mpjaodan
    vtoclg
    anabsi7
    @0
    @3
    @6
    wceq
    wph
    @0
    @2
    cE
    cabs
    vx
    cD
    cA
    cE
    cz
    @0
    vx
    cE
    nfcvd
    oddcomabszz.6
    csbiegf
    fveq2d
    adantl
    @5
    cF
    wceq
    @1
    vx
    @4
    cA
    cF
    cD
    cabs
    fvex
    oddcomabszz.7
    csbie
    a1i
    3eqtr3d
end
