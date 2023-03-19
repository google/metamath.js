include "ccom.mm"
include "wfun.mm"
include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "ciun.mm"
include "funmpt2.mm"
include "funco.mm"
include "mp2an.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "wral.mm"
include "crn.mm"
include "wss.mm"
include "ssv.mm"
include "ovex.mm"
include "iunex.mm"
include "dmmpti.mm"
include "sseqtr4i.mm"
include "dmcosseq.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "cun.mm"
include "unex.mm"
include "eqeltri.mm"
include "eqtr4i.mm"
include "wcel.mm"
include "vex.mm"
include "eleqtrri.mm"
include "fvco.mm"
include "weq.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "fvmpt.mm"
include "fveq2i.mm"
include "3eqtri.mm"
include "eqeq12i.mm"
include "raleqbii.mm"
include "iunxun.mm"
include "unssi.mm"
include "eqsstri.mm"
include "eqssi.mm"
include "iuneq1.mm"
include "a1i.mm"
include "mprgbir.mm"
include "eqfunfv.mm"
include "biimprd.mm"
include "mp2ani.mm"

theorem comptiunov2i
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let c.ex: class .^
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume comptiunov2.x: |- X = ( a e. _V |-> U_ i e. I ( a .^ i ) )
  assume comptiunov2.y: |- Y = ( b e. _V |-> U_ j e. J ( b .^ j ) )
  assume comptiunov2.z: |- Z = ( c e. _V |-> U_ k e. K ( c .^ k ) )
  assume comptiunov2.i: |- I e. _V
  assume comptiunov2.j: |- J e. _V
  assume comptiunov2.k: |- K = ( I u. J )
  assume comptiunov2.1: |- U_ k e. I ( d .^ k ) C_ U_ i e. I ( U_ j e. J ( d .^ j ) .^ i )
  assume comptiunov2.2: |- U_ k e. J ( d .^ k ) C_ U_ i e. I ( U_ j e. J ( d .^ j ) .^ i )
  assume comptiunov2.3: |- U_ i e. I ( U_ j e. J ( d .^ j ) .^ i ) C_ U_ k e. ( I u. J ) ( d .^ k )

  disjoint a i
  disjoint .^ a
  disjoint .^ i
  disjoint .^ b
  disjoint .^ c
  disjoint I a
  disjoint I i
  disjoint I k
  disjoint a j
  disjoint J a
  disjoint i j
  disjoint J i
  disjoint J j
  disjoint J b
  disjoint J k
  disjoint c k
  disjoint K c
  disjoint K k
  disjoint X d
  disjoint Y d
  disjoint Z d
  disjoint a d
  disjoint d i
  disjoint d j
  disjoint b d
  disjoint b j
  disjoint c d
  disjoint d k
  assert |- ( X o. Y ) = Z

  proof
    cX
    cY
    ccom
    #
    wfun
    #
    cZ
    wfun
    #
    @0
    cZ
    wceq
    #
    cX
    wfun
    cY
    wfun
    #
    @1
    va
    cvv
    vi
    cI
    va
    cv
    #
    vi
    cv
    #
    c.ex
    co
    #
    ciun
    #
    cX
    comptiunov2.x
    funmpt2
    vb
    cvv
    vj
    cJ
    vb
    cv
    #
    vj
    cv
    #
    c.ex
    co
    #
    ciun
    #
    cY
    comptiunov2.y
    funmpt2
    #
    cX
    cY
    funco
    mp2an
    vc
    cvv
    vk
    cK
    vc
    cv
    #
    vk
    cv
    #
    c.ex
    co
    #
    ciun
    #
    cZ
    comptiunov2.z
    funmpt2
    @1
    @2
    wa
    #
    @0
    cdm
    #
    cZ
    cdm
    #
    wceq
    #
    vd
    cv
    #
    @0
    cfv
    #
    @22
    cZ
    cfv
    #
    wceq
    #
    vd
    @19
    wral
    #
    @3
    @19
    cvv
    @20
    @19
    cY
    cdm
    #
    cvv
    cY
    crn
    #
    cX
    cdm
    #
    wss
    @19
    @27
    wceq
    @28
    cvv
    @29
    @28
    ssv
    va
    cvv
    @8
    cX
    vi
    cI
    @7
    comptiunov2.i
    @5
    @6
    c.ex
    ovex
    iunex
    comptiunov2.x
    dmmpti
    sseqtr4i
    cX
    cY
    dmcosseq
    ax-mp
    vb
    cvv
    @12
    cY
    vj
    cJ
    @11
    comptiunov2.j
    @9
    @10
    c.ex
    ovex
    iunex
    comptiunov2.y
    dmmpti
    #
    eqtri
    #
    vc
    cvv
    @17
    cZ
    vk
    cK
    @16
    cK
    cI
    cJ
    cun
    #
    cvv
    comptiunov2.k
    cI
    cJ
    comptiunov2.i
    comptiunov2.j
    unex
    eqeltri
    #
    @14
    @15
    c.ex
    ovex
    iunex
    comptiunov2.z
    dmmpti
    eqtr4i
    @26
    vi
    cI
    vj
    cJ
    @22
    @10
    c.ex
    co
    #
    ciun
    #
    @6
    c.ex
    co
    #
    ciun
    #
    vk
    cK
    @22
    @15
    c.ex
    co
    #
    ciun
    #
    wceq
    #
    vd
    cvv
    @25
    @40
    vd
    @19
    cvv
    @31
    @23
    @37
    @24
    @39
    @23
    @22
    cY
    cfv
    #
    cX
    cfv
    #
    @35
    cX
    cfv
    #
    @37
    @4
    @22
    @27
    wcel
    @23
    @42
    wceq
    @13
    @22
    cvv
    @27
    vd
    vex
    #
    @30
    eleqtrri
    @22
    cX
    cY
    fvco
    mp2an
    @41
    @35
    cX
    @22
    cvv
    wcel
    #
    @41
    @35
    wceq
    @44
    vb
    @22
    @12
    @35
    cvv
    cY
    vb
    vd
    weq
    vj
    cJ
    @11
    @34
    @9
    @22
    @10
    c.ex
    oveq1
    iuneq2d
    comptiunov2.y
    vj
    cJ
    @34
    comptiunov2.j
    @22
    @10
    c.ex
    ovex
    iunex
    #
    fvmpt
    ax-mp
    fveq2i
    @35
    cvv
    wcel
    @43
    @37
    wceq
    @46
    va
    @35
    @8
    @37
    cvv
    cX
    @5
    @35
    wceq
    vi
    cI
    @7
    @36
    @5
    @35
    @6
    c.ex
    oveq1
    iuneq2d
    comptiunov2.x
    vi
    cI
    @36
    comptiunov2.i
    @35
    @6
    c.ex
    ovex
    iunex
    fvmpt
    ax-mp
    3eqtri
    @45
    @24
    @39
    wceq
    @44
    vc
    @22
    @17
    @39
    cvv
    cZ
    vc
    vd
    weq
    vk
    cK
    @16
    @38
    @14
    @22
    @15
    c.ex
    oveq1
    iuneq2d
    comptiunov2.z
    vk
    cK
    @38
    @33
    @22
    @15
    c.ex
    ovex
    iunex
    fvmpt
    ax-mp
    eqeq12i
    raleqbii
    @40
    @45
    @37
    vk
    @32
    @38
    ciun
    #
    @39
    @37
    @47
    comptiunov2.3
    @47
    vk
    cI
    @38
    ciun
    #
    vk
    cJ
    @38
    ciun
    #
    cun
    @37
    vk
    cI
    cJ
    @38
    iunxun
    @48
    @49
    @37
    comptiunov2.1
    comptiunov2.2
    unssi
    eqsstri
    eqssi
    cK
    @32
    wceq
    @39
    @47
    wceq
    comptiunov2.k
    vk
    cK
    @32
    @38
    iuneq1
    ax-mp
    eqtr4i
    a1i
    mprgbir
    @18
    @3
    @21
    @26
    wa
    vd
    @0
    cZ
    eqfunfv
    biimprd
    mp2ani
    mp2an
end
