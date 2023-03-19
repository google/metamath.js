include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "cima.mm"
include "wceq.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf1o.mm"
include "wfun.mm"
include "wi.mm"
include "simpll.mm"
include "simprl1.mm"
include "simplr1.mm"
include "simprl2.mm"
include "sseldd.mm"
include "simprr.mm"
include "axcontlem2.mm"
include "syl31anc.mm"
include "f1ofun.mm"
include "fvelima.mm"
include "ex.mm"
include "3syl.mm"
include "reeanv.mm"
include "simplr3.mm"
include "breq1.mm"
include "opeq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "wb.mm"
include "simplll.mm"
include "adantr.mm"
include "3jca.mm"
include "simplrr.mm"
include "axcontlem4.mm"
include "sseld.mm"
include "simpl.mm"
include "axcontlem3.mm"
include "syl13anc.mm"
include "anim12d.mm"
include "imp.mm"
include "axcontlem7.mm"
include "syl21anc.mm"
include "mpbid.mm"
include "breq12.mm"
include "syl5ibcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "syl2and.mm"
include "ralrimivv.mm"

theorem axcontlem9
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assume axcontlem9.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }
  assume axcontlem9.2: |- F = { <. x , t >. | ( x e. D /\ ( t e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( x ` i ) = ( ( ( 1 - t ) x. ( Z ` i ) ) + ( t x. ( U ` i ) ) ) ) ) }

  disjoint A m
  disjoint A n
  disjoint A p
  disjoint A x
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint n p
  disjoint n x
  disjoint p x
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint m y
  disjoint n y
  disjoint p y
  disjoint x y
  disjoint D t
  disjoint t x
  disjoint D x
  disjoint F i
  disjoint F m
  disjoint F t
  disjoint i p
  disjoint i t
  disjoint i x
  disjoint p t
  disjoint N i
  disjoint N m
  disjoint N n
  disjoint N p
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint U i
  disjoint U m
  disjoint U n
  disjoint U p
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint Z i
  disjoint Z m
  disjoint Z n
  disjoint Z p
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint F p
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  disjoint D a
  disjoint D b
  disjoint a i
  disjoint b i
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a m
  disjoint b m
  disjoint a n
  disjoint b n
  disjoint a t
  disjoint b t
  disjoint N a
  disjoint N b
  disjoint U a
  disjoint U b
  disjoint Z a
  disjoint Z b
  assert |- ( ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ A. x e. A A. y e. B x Btwn <. Z , y >. ) ) /\ ( ( Z e. ( EE ` N ) /\ U e. A /\ B =/= (/) ) /\ Z =/= U ) ) -> A. n e. ( F " A ) A. m e. ( F " B ) n <_ m )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wss
    #
    cB
    @1
    wss
    #
    vx
    cv
    #
    cZ
    vy
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    w3a
    #
    wa
    #
    cZ
    @1
    wcel
    #
    cU
    cA
    wcel
    #
    cB
    c0
    wne
    #
    w3a
    #
    cZ
    cU
    wne
    #
    wa
    #
    wa
    #
    vn
    cv
    #
    vm
    cv
    #
    cle
    wbr
    #
    vn
    vm
    cF
    cA
    cima
    #
    cF
    cB
    cima
    #
    @17
    @18
    @21
    wcel
    #
    va
    cv
    #
    cF
    cfv
    #
    @18
    wceq
    #
    va
    cA
    wrex
    #
    @19
    @22
    wcel
    #
    vb
    cv
    #
    cF
    cfv
    #
    @19
    wceq
    #
    vb
    cB
    wrex
    #
    @20
    @17
    cD
    cc0
    cpnf
    cico
    co
    #
    cF
    wf1o
    #
    cF
    wfun
    #
    @23
    @27
    wi
    @17
    @0
    @11
    cU
    @1
    wcel
    #
    @15
    @34
    @0
    @9
    @16
    simpll
    @11
    @12
    @13
    @15
    @10
    simprl1
    #
    @17
    cA
    @1
    cU
    @2
    @3
    @8
    @0
    @16
    simplr1
    @11
    @12
    @13
    @15
    @10
    simprl2
    #
    sseldd
    #
    @10
    @14
    @15
    simprr
    #
    vx
    vt
    cD
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem9.1
    axcontlem9.2
    axcontlem2
    syl31anc
    #
    cD
    @33
    cF
    f1ofun
    #
    @35
    @23
    @27
    va
    @18
    cA
    cF
    fvelima
    ex
    3syl
    @17
    @34
    @35
    @28
    @32
    wi
    @41
    @42
    @35
    @28
    @32
    vb
    @19
    cB
    cF
    fvelima
    ex
    3syl
    @27
    @32
    wa
    @26
    @31
    wa
    #
    vb
    cB
    wrex
    va
    cA
    wrex
    @17
    @20
    @26
    @31
    va
    vb
    cA
    cB
    reeanv
    @17
    @43
    @20
    va
    vb
    cA
    cB
    @17
    @24
    cA
    wcel
    #
    @29
    cB
    wcel
    #
    wa
    #
    wa
    #
    @25
    @30
    cle
    wbr
    #
    @43
    @20
    @47
    @24
    cZ
    @29
    cop
    #
    cbtwn
    wbr
    #
    @48
    @17
    @8
    @46
    @50
    @2
    @3
    @8
    @0
    @16
    simplr3
    @7
    @50
    @24
    @6
    cbtwn
    wbr
    vx
    vy
    @24
    @29
    cA
    cB
    @4
    @24
    @6
    cbtwn
    breq1
    @5
    @29
    wceq
    @6
    @49
    @24
    cbtwn
    @5
    @29
    cZ
    opeq2
    breq2d
    rspc2v
    mpan9
    @47
    @0
    @11
    @36
    w3a
    @15
    @24
    cD
    wcel
    #
    @29
    cD
    wcel
    #
    wa
    #
    @50
    @48
    wb
    @47
    @0
    @11
    @36
    @0
    @9
    @16
    @46
    simplll
    @17
    @11
    @46
    @37
    adantr
    @17
    @36
    @46
    @39
    adantr
    3jca
    @10
    @14
    @15
    @46
    simplrr
    @17
    @46
    @53
    @17
    @44
    @51
    @45
    @52
    @17
    cA
    cD
    @24
    vx
    vy
    cA
    cB
    cD
    cU
    cN
    cZ
    vp
    axcontlem9.1
    axcontlem4
    sseld
    @17
    cB
    cD
    @29
    @17
    @10
    @11
    @12
    @15
    cB
    cD
    wss
    @10
    @16
    simpl
    @37
    @38
    @40
    vx
    vy
    cA
    cB
    cD
    cU
    cN
    cZ
    vp
    axcontlem9.1
    axcontlem3
    syl13anc
    sseld
    anim12d
    imp
    vx
    vt
    cD
    @24
    @29
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem9.1
    axcontlem9.2
    axcontlem7
    syl21anc
    mpbid
    @25
    @18
    @30
    @19
    cle
    breq12
    syl5ibcom
    rexlimdvva
    syl5bir
    syl2and
    ralrimivv
end
