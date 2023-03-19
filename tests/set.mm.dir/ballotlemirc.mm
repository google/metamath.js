include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "ballotlemrc.mm"
include "ballotlemi.mm"
include "syl.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "cz.mm"
include "ballotlemiex.mm"
include "simpld.mm"
include "elfzelz.mm"
include "zred.mm"
include "cfn.mm"
include "cin.mm"
include "chash.mm"
include "cmin.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ballotlemfrci.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "elrabi.mm"
include "anim2i.mm"
include "simpr.mm"
include "w3a.mm"
include "ballotlemfrcn0.mm"
include "neneqd.mm"
include "simprbi.mm"
include "nsyl.mm"
include "3expa.mm"
include "syldan.mm"
include "ex.mm"
include "con2d.mm"
include "imp.mm"
include "sylancom.mm"
include "infmin.mm"
include "eqtrd.mm"

theorem ballotlemirc
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let vj: setvar j
  let vd: setvar d
  let cJ: class J
  let cD: class D
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )
  assume ballotth.r: |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) )

  disjoint k x
  disjoint C x
  disjoint F x
  disjoint M x
  disjoint N x
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint C i
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint C k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint R k
  disjoint k y
  disjoint x y
  disjoint C y
  disjoint E y
  disjoint F y
  disjoint I y
  disjoint M y
  disjoint N y
  disjoint O y
  disjoint R y
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint I u
  disjoint I v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  disjoint u y
  disjoint v y
  disjoint i y
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint J k
  disjoint D i
  disjoint D k
  assert |- ( C e. ( O \ E ) -> ( I ` ( R ` C ) ) = ( I ` C ) )

  proof
    cC
    cO
    cE
    cdif
    #
    wcel
    #
    cC
    cR
    cfv
    #
    cI
    cfv
    #
    vk
    cv
    #
    @2
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    vk
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    crab
    #
    cr
    clt
    cinf
    #
    cC
    cI
    cfv
    #
    @1
    @2
    @0
    wcel
    @3
    @11
    wceq
    vx
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemrc
    vx
    @2
    cP
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotlemi
    syl
    @1
    vy
    cr
    @10
    @12
    clt
    cr
    clt
    wor
    @1
    ltso
    a1i
    @1
    @12
    @1
    @12
    @9
    wcel
    #
    @12
    cz
    wcel
    @1
    @13
    @12
    cC
    cF
    cfv
    cfv
    cc0
    wceq
    vx
    cC
    cP
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotlemiex
    simpld
    #
    @12
    c1
    @8
    elfzelz
    syl
    zred
    @1
    @13
    @12
    @5
    cfv
    #
    cc0
    wceq
    #
    @12
    @10
    wcel
    @14
    vx
    vv
    vu
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    vu
    vv
    cfn
    cfn
    vv
    cv
    #
    vu
    cv
    #
    cin
    chash
    cfv
    @17
    @18
    cdif
    chash
    cfv
    cmin
    co
    cmpt2
    #
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    @19
    eqid
    ballotlemfrci
    @7
    @16
    vk
    @12
    @9
    @4
    @12
    wceq
    @6
    @15
    cc0
    @4
    @12
    @5
    fveq2
    eqeq1d
    elrab
    sylanbrc
    @1
    vy
    cv
    #
    @10
    wcel
    #
    @1
    @20
    @9
    wcel
    #
    wa
    #
    @20
    @12
    clt
    wbr
    #
    wn
    #
    @21
    @22
    @1
    @7
    vk
    @20
    @9
    elrabi
    anim2i
    @23
    @21
    @25
    @23
    @24
    @21
    @23
    @24
    @21
    wn
    #
    @23
    @24
    @24
    @26
    @23
    @24
    simpr
    @1
    @22
    @24
    @26
    @1
    @22
    @24
    w3a
    #
    @20
    @5
    cfv
    #
    cc0
    wceq
    #
    @21
    @27
    @28
    cc0
    vx
    cC
    cP
    cR
    cS
    vi
    vk
    cE
    cF
    cI
    @20
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotth.r
    ballotlemfrcn0
    neneqd
    @21
    @22
    @29
    @7
    @29
    vk
    @20
    @9
    @4
    @20
    wceq
    @6
    @28
    cc0
    @4
    @20
    @5
    fveq2
    eqeq1d
    elrab
    simprbi
    nsyl
    3expa
    syldan
    ex
    con2d
    imp
    sylancom
    infmin
    eqtrd
end
