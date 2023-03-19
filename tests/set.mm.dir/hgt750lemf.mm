include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cvma.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "csu.mm"
include "cexp.mm"
include "cle.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cr.mm"
include "wf.mm"
include "vmaf.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "adantr.mm"
include "sseldi.mm"
include "remulcld.mm"
include "resqcld.mm"
include "recnd.mm"
include "mul4d.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "wbr.mm"
include "vmage0.mm"
include "syl.mm"
include "mulge0d.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "rspcdva.mm"
include "lemul12ad.mm"
include "sqvald.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "lemul1ad.mm"
include "eqbrtrrd.mm"
include "fsumle.mm"
include "fsummulc2.mm"

theorem hgt750lemf
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let vm: setvar m
  let vn: setvar n
  let cH: class H
  let cK: class K
  assume hgt750lemf.a: |- ( ph -> A e. Fin )
  assume hgt750lemf.p: |- ( ph -> P e. RR )
  assume hgt750lemf.q: |- ( ph -> Q e. RR )
  assume hgt750lemf.h: |- ( ph -> H : NN --> ( 0 [,) +oo ) )
  assume hgt750lemf.k: |- ( ph -> K : NN --> ( 0 [,) +oo ) )
  assume hgt750lemf.0: |- ( ( ph /\ n e. A ) -> ( n ` 0 ) e. NN )
  assume hgt750lemf.1: |- ( ( ph /\ n e. A ) -> ( n ` 1 ) e. NN )
  assume hgt750lemf.2: |- ( ( ph /\ n e. A ) -> ( n ` 2 ) e. NN )
  assume hgt750lemf.3: |- ( ( ph /\ m e. NN ) -> ( K ` m ) <_ P )
  assume hgt750lemf.4: |- ( ( ph /\ m e. NN ) -> ( H ` m ) <_ Q )

  disjoint A m
  disjoint A n
  disjoint m n
  disjoint H m
  disjoint K m
  disjoint P m
  disjoint P n
  disjoint Q m
  disjoint Q n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> sum_ n e. A ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) ) x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) ) x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) ) <_ ( ( ( P ^ 2 ) x. Q ) x. sum_ n e. A ( ( Lam ` ( n ` 0 ) ) x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) ) ) )

  proof
    wph
    cA
    cc0
    vn
    cv
    #
    cfv
    #
    cvma
    cfv
    #
    @1
    cH
    cfv
    #
    cmul
    co
    #
    c1
    @0
    cfv
    #
    cvma
    cfv
    #
    @5
    cK
    cfv
    #
    cmul
    co
    #
    c2
    @0
    cfv
    #
    cvma
    cfv
    #
    @9
    cK
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vn
    csu
    cA
    cP
    c2
    cexp
    co
    #
    cQ
    cmul
    co
    #
    @2
    @6
    @10
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vn
    csu
    @16
    cA
    @18
    vn
    csu
    cmul
    co
    cle
    wph
    cA
    @14
    @19
    vn
    hgt750lemf.a
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @4
    @13
    @21
    @2
    @3
    @21
    cn
    cr
    @1
    cvma
    cn
    cr
    cvma
    wf
    @21
    vmaf
    a1i
    #
    hgt750lemf.0
    ffvelrnd
    #
    @21
    cc0
    cpnf
    cico
    co
    #
    cr
    @3
    rge0ssre
    @21
    cn
    @24
    @1
    cH
    wph
    cn
    @24
    cH
    wf
    @20
    hgt750lemf.h
    adantr
    hgt750lemf.0
    ffvelrnd
    #
    sseldi
    #
    remulcld
    @21
    @8
    @12
    @21
    @6
    @7
    @21
    cn
    cr
    @5
    cvma
    @22
    hgt750lemf.1
    ffvelrnd
    #
    @21
    @24
    cr
    @7
    rge0ssre
    @21
    cn
    @24
    @5
    cK
    wph
    cn
    @24
    cK
    wf
    @20
    hgt750lemf.k
    adantr
    #
    hgt750lemf.1
    ffvelrnd
    #
    sseldi
    #
    remulcld
    @21
    @10
    @11
    @21
    cn
    cr
    @9
    cvma
    @22
    hgt750lemf.2
    ffvelrnd
    #
    @21
    @24
    cr
    @11
    rge0ssre
    @21
    cn
    @24
    @9
    cK
    @28
    hgt750lemf.2
    ffvelrnd
    #
    sseldi
    #
    remulcld
    remulcld
    remulcld
    @21
    @16
    @18
    wph
    @16
    cr
    wcel
    @20
    wph
    @15
    cQ
    wph
    cP
    hgt750lemf.p
    resqcld
    #
    hgt750lemf.q
    remulcld
    #
    adantr
    #
    @21
    @2
    @17
    @23
    @21
    @6
    @10
    @27
    @31
    remulcld
    #
    remulcld
    #
    remulcld
    @21
    @3
    @7
    @11
    cmul
    co
    #
    cmul
    co
    #
    @18
    cmul
    co
    #
    @14
    @19
    cle
    @21
    @18
    @40
    cmul
    co
    @4
    @17
    @39
    cmul
    co
    #
    cmul
    co
    @41
    @14
    @21
    @2
    @17
    @3
    @39
    @21
    @2
    @23
    recnd
    #
    @21
    @17
    @37
    recnd
    #
    @21
    @3
    @26
    recnd
    #
    @21
    @39
    @21
    @7
    @11
    @30
    @33
    remulcld
    #
    recnd
    #
    mul4d
    @21
    @18
    @40
    @21
    @2
    @17
    @43
    @44
    mulcld
    @21
    @3
    @39
    @45
    @47
    mulcld
    mulcomd
    @21
    @42
    @13
    @4
    cmul
    @21
    @6
    @10
    @7
    @11
    @21
    @6
    @27
    recnd
    @21
    @10
    @31
    recnd
    @21
    @7
    @30
    recnd
    @21
    @11
    @33
    recnd
    mul4d
    oveq2d
    3eqtr3d
    @21
    @40
    @16
    @18
    @21
    @3
    @39
    @26
    @46
    remulcld
    @36
    @38
    @21
    @2
    @17
    @23
    @37
    @21
    @1
    cn
    wcel
    cc0
    @2
    cle
    wbr
    hgt750lemf.0
    @1
    vmage0
    syl
    @21
    @6
    @10
    @27
    @31
    @21
    @5
    cn
    wcel
    cc0
    @6
    cle
    wbr
    hgt750lemf.1
    @5
    vmage0
    syl
    @21
    @9
    cn
    wcel
    cc0
    @10
    cle
    wbr
    hgt750lemf.2
    @9
    vmage0
    syl
    mulge0d
    mulge0d
    @21
    @40
    cQ
    cP
    cP
    cmul
    co
    #
    cmul
    co
    #
    @16
    cle
    @21
    @3
    cQ
    @39
    @48
    @26
    wph
    cQ
    cr
    wcel
    @20
    hgt750lemf.q
    adantr
    @46
    wph
    @48
    cr
    wcel
    @20
    wph
    cP
    cP
    hgt750lemf.p
    hgt750lemf.p
    remulcld
    adantr
    @21
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @3
    @24
    wcel
    cc0
    @3
    cle
    wbr
    @50
    @21
    0xr
    a1i
    #
    @51
    @21
    pnfxr
    a1i
    #
    @25
    cc0
    cpnf
    @3
    icogelb
    syl3anc
    @21
    @7
    @11
    @30
    @33
    @21
    @50
    @51
    @7
    @24
    wcel
    cc0
    @7
    cle
    wbr
    @52
    @53
    @29
    cc0
    cpnf
    @7
    icogelb
    syl3anc
    #
    @21
    @50
    @51
    @11
    @24
    wcel
    cc0
    @11
    cle
    wbr
    @52
    @53
    @32
    cc0
    cpnf
    @11
    icogelb
    syl3anc
    #
    mulge0d
    @21
    vm
    cv
    #
    cH
    cfv
    #
    cQ
    cle
    wbr
    #
    @3
    cQ
    cle
    wbr
    vm
    cn
    @1
    @56
    @1
    wceq
    @57
    @3
    cQ
    cle
    @56
    @1
    cH
    fveq2
    breq1d
    wph
    @58
    vm
    cn
    wral
    @20
    wph
    @58
    vm
    cn
    hgt750lemf.4
    ralrimiva
    adantr
    hgt750lemf.0
    rspcdva
    @21
    @7
    cP
    @11
    cP
    @30
    wph
    cP
    cr
    wcel
    @20
    hgt750lemf.p
    adantr
    #
    @33
    @59
    @54
    @55
    @21
    @56
    cK
    cfv
    #
    cP
    cle
    wbr
    #
    @7
    cP
    cle
    wbr
    vm
    cn
    @5
    @56
    @5
    wceq
    @60
    @7
    cP
    cle
    @56
    @5
    cK
    fveq2
    breq1d
    wph
    @61
    vm
    cn
    wral
    @20
    wph
    @61
    vm
    cn
    hgt750lemf.3
    ralrimiva
    adantr
    #
    hgt750lemf.1
    rspcdva
    @21
    @61
    @11
    cP
    cle
    wbr
    vm
    cn
    @9
    @56
    @9
    wceq
    @60
    @11
    cP
    cle
    @56
    @9
    cK
    fveq2
    breq1d
    @62
    hgt750lemf.2
    rspcdva
    lemul12ad
    lemul12ad
    wph
    @16
    @49
    wceq
    @20
    wph
    @16
    cQ
    @15
    cmul
    co
    @49
    wph
    @15
    cQ
    wph
    @15
    @34
    recnd
    wph
    cQ
    hgt750lemf.q
    recnd
    mulcomd
    wph
    @15
    @48
    cQ
    cmul
    wph
    cP
    wph
    cP
    hgt750lemf.p
    recnd
    sqvald
    oveq2d
    eqtrd
    adantr
    breqtrrd
    lemul1ad
    eqbrtrrd
    fsumle
    wph
    cA
    @18
    @16
    vn
    hgt750lemf.a
    wph
    @16
    @35
    recnd
    @21
    @18
    @38
    recnd
    fsummulc2
    breqtrrd
end
