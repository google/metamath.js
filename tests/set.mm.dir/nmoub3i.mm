include "wf.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cabs.mm"
include "wa.mm"
include "c1.mm"
include "wi.mm"
include "cnv.mm"
include "nvcl.mm"
include "mpan.mm"
include "remulcl.mm"
include "sylan2.mm"
include "adantr.mm"
include "recn.mm"
include "abscld.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "cc0.mm"
include "simpl.mm"
include "nvge0.mm"
include "jca.mm"
include "adantl.mm"
include "leabs.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "w3a.mm"
include "1red.mm"
include "absge0d.mm"
include "3jca.mm"
include "lemul2a.mm"
include "sylan.mm"
include "wceq.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "adantlll.mm"
include "ffvelrn.mm"
include "sylancr.mm"
include "adantlr.mm"
include "adantll.mm"
include "ad2antlr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ex.mm"
include "com23.mm"
include "ralimdva.mm"
include "imp.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "nmoubi.mm"
include "biimpar.mm"
include "syldan.mm"
include "3impa.mm"

theorem nmoub3i
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vy: setvar y
  assume nmoubi.1: |- X = ( BaseSet ` U )
  assume nmoubi.y: |- Y = ( BaseSet ` W )
  assume nmoubi.l: |- L = ( normCV ` U )
  assume nmoubi.m: |- M = ( normCV ` W )
  assume nmoubi.3: |- N = ( U normOpOLD W )
  assume nmoubi.u: |- U e. NrmCVec
  assume nmoubi.w: |- W e. NrmCVec

  disjoint A x
  disjoint L x
  disjoint U x
  disjoint W x
  disjoint Y x
  disjoint M x
  disjoint T x
  disjoint X x
  disjoint x z
  disjoint A z
  disjoint f k
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint L f
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint L k
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint L r
  disjoint x y
  disjoint y z
  disjoint L y
  disjoint L z
  disjoint U y
  disjoint W y
  disjoint Y k
  disjoint Y r
  disjoint Y y
  disjoint M f
  disjoint M k
  disjoint M r
  disjoint M y
  disjoint M z
  disjoint T f
  disjoint T k
  disjoint T r
  disjoint T y
  disjoint T z
  disjoint X f
  disjoint X k
  disjoint X r
  disjoint X y
  disjoint X z
  disjoint N k
  disjoint N r
  disjoint N y
  assert |- ( ( T : X --> Y /\ A e. RR /\ A. x e. X ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ ( abs ` A ) )

  proof
    cX
    cY
    cT
    wf
    #
    cA
    cr
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    #
    cM
    cfv
    #
    cA
    @2
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    cX
    wral
    #
    cT
    cN
    cfv
    cA
    cabs
    cfv
    #
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @8
    @5
    c1
    cle
    wbr
    #
    @4
    @9
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    @10
    @11
    @8
    @15
    @11
    @7
    @14
    vx
    cX
    @11
    @2
    cX
    wcel
    #
    wa
    #
    @12
    @7
    @13
    @17
    @12
    @7
    @13
    wi
    @17
    @12
    wa
    @7
    @6
    @9
    cle
    wbr
    #
    @13
    @1
    @16
    @12
    @18
    @0
    @1
    @16
    wa
    #
    @12
    wa
    #
    @6
    @9
    @5
    cmul
    co
    #
    @9
    @19
    @6
    cr
    wcel
    #
    @12
    @16
    @1
    @5
    cr
    wcel
    #
    @22
    cU
    cnv
    wcel
    #
    @16
    @23
    nmoubi.u
    @2
    cU
    cL
    cX
    nmoubi.1
    nmoubi.l
    nvcl
    mpan
    #
    cA
    @5
    remulcl
    sylan2
    #
    adantr
    @19
    @21
    cr
    wcel
    #
    @12
    @1
    @9
    cr
    wcel
    #
    @23
    @27
    @16
    @1
    cA
    cA
    recn
    #
    abscld
    #
    @25
    @9
    @5
    remulcl
    syl2an
    adantr
    @1
    @28
    @16
    @12
    @30
    ad2antrr
    @19
    @6
    @21
    cle
    wbr
    #
    @12
    @19
    @1
    @28
    @23
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    cA
    @9
    cle
    wbr
    #
    @31
    @1
    @16
    simpl
    @1
    @28
    @16
    @30
    adantr
    #
    @16
    @33
    @1
    @16
    @23
    @32
    @25
    @24
    @16
    @32
    nmoubi.u
    @2
    cU
    cL
    cX
    nmoubi.1
    nmoubi.l
    nvge0
    mpan
    jca
    adantl
    @1
    @34
    @16
    cA
    leabs
    adantr
    cA
    @9
    @5
    lemul1a
    syl31anc
    adantr
    @20
    @21
    @9
    c1
    cmul
    co
    #
    @9
    cle
    @19
    @23
    c1
    cr
    wcel
    #
    @28
    cc0
    @9
    cle
    wbr
    #
    wa
    #
    w3a
    @12
    @21
    @36
    cle
    wbr
    @19
    @23
    @37
    @39
    @16
    @23
    @1
    @25
    adantl
    @19
    1red
    @19
    @28
    @38
    @35
    @1
    @38
    @16
    @1
    cA
    @29
    absge0d
    adantr
    jca
    3jca
    @5
    c1
    @9
    lemul2a
    sylan
    @1
    @36
    @9
    wceq
    @16
    @12
    @1
    @9
    @1
    @9
    @30
    recnd
    mulid1d
    ad2antrr
    breqtrd
    letrd
    adantlll
    @17
    @7
    @18
    wa
    @13
    wi
    #
    @12
    @17
    @4
    cr
    wcel
    #
    @22
    @28
    @40
    @0
    @16
    @41
    @1
    @0
    @16
    wa
    cW
    cnv
    wcel
    @3
    cY
    wcel
    @41
    nmoubi.w
    cX
    cY
    @2
    cT
    ffvelrn
    @3
    cW
    cM
    cY
    nmoubi.y
    nmoubi.m
    nvcl
    sylancr
    adantlr
    @1
    @16
    @22
    @0
    @26
    adantll
    @1
    @28
    @0
    @16
    @30
    ad2antlr
    @4
    @6
    @9
    letr
    syl3anc
    adantr
    mpan2d
    ex
    com23
    ralimdva
    imp
    @11
    @10
    @15
    @1
    @0
    @9
    cxr
    wcel
    @10
    @15
    wb
    @1
    @9
    @30
    rexrd
    vx
    @9
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    cY
    nmoubi.1
    nmoubi.y
    nmoubi.l
    nmoubi.m
    nmoubi.3
    nmoubi.u
    nmoubi.w
    nmoubi
    sylan2
    biimpar
    syldan
    3impa
end
