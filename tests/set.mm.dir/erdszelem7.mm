include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "crab.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "wfun.mm"
include "cvv.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "hashf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "erdszelem5.mm"
include "mpdan.mm"
include "fvelima.mm"
include "sylancr.mm"
include "wss.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "erdszelem1.mm"
include "simprl1.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "3syl.mm"
include "adantr.mm"
include "sstrd.mm"
include "selpw.mm"
include "sylibr.mm"
include "wn.mm"
include "cmin.mm"
include "cz.mm"
include "wb.mm"
include "cn.mm"
include "erdszelem6.mm"
include "ffvelrnd.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnz.mm"
include "peano2zm.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "nnltlem1.mm"
include "bitr4d.mm"
include "mtbid.mm"
include "nnred.mm"
include "cr.mm"
include "cfn.mm"
include "erdszelem2.mm"
include "simpri.mm"
include "nnssre.mm"
include "sstri.mm"
include "sseldi.mm"
include "lenltd.mm"
include "mpbird.mm"
include "simprr.mm"
include "breqtrrd.mm"
include "simprl2.mm"
include "jca32.mm"
include "expr.mm"
include "sylan2b.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem erdszelem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cF: class F
  let cK: class K
  let cN: class N
  let cO: class O
  let vs: setvar s
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let cS: class S
  let cT: class T
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.k: |- K = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.o: |- O Or RR
  assume erdszelem.a: |- ( ph -> A e. ( 1 ... N ) )
  assume erdszelem7.r: |- ( ph -> R e. NN )
  assume erdszelem7.m: |- ( ph -> -. ( K ` A ) e. ( 1 ... ( R - 1 ) ) )

  disjoint x y
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint K s
  disjoint A s
  disjoint A x
  disjoint A y
  disjoint O s
  disjoint O x
  disjoint O y
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint N s
  disjoint N x
  disjoint N y
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s w
  disjoint s z
  disjoint F w
  disjoint F z
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint I y
  disjoint K f
  disjoint K z
  disjoint A f
  disjoint A w
  disjoint A z
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint O f
  disjoint O w
  disjoint O z
  disjoint R m
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint N m
  disjoint N n
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ph -> E. s e. ~P ( 1 ... N ) ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , O ( s , ( F " s ) ) ) )

  proof
    wph
    vs
    cv
    #
    chash
    cfv
    #
    cA
    cK
    cfv
    #
    wceq
    #
    vs
    vy
    cv
    #
    cF
    @4
    cima
    clt
    cO
    cF
    @4
    cres
    wiso
    cA
    @4
    wcel
    wa
    vy
    c1
    cA
    cfz
    co
    #
    cpw
    crab
    #
    wrex
    #
    cR
    @1
    cle
    wbr
    #
    @0
    cF
    @0
    cima
    clt
    cO
    cF
    @0
    cres
    wiso
    #
    wa
    #
    vs
    c1
    cN
    cfz
    co
    #
    cpw
    #
    wrex
    wph
    chash
    wfun
    #
    @2
    chash
    @6
    cima
    #
    wcel
    #
    @7
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    @13
    hashf
    cvv
    @16
    chash
    ffun
    ax-mp
    wph
    cA
    @11
    wcel
    #
    @15
    erdszelem.a
    wph
    vx
    vy
    cA
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem.o
    erdszelem5
    mpdan
    #
    vs
    @2
    @6
    chash
    fvelima
    sylancr
    wph
    @3
    @10
    vs
    @6
    @12
    wph
    @0
    @6
    wcel
    #
    @3
    @0
    @12
    wcel
    #
    @10
    wa
    #
    @19
    wph
    @0
    @5
    wss
    #
    @9
    cA
    @0
    wcel
    #
    w3a
    #
    @3
    @21
    wi
    vy
    cA
    @6
    cF
    cO
    @0
    @6
    eqid
    #
    erdszelem1
    wph
    @24
    @3
    @21
    wph
    @24
    @3
    wa
    #
    wa
    #
    @20
    @8
    @9
    @27
    @0
    @11
    wss
    @20
    @27
    @0
    @5
    @11
    @22
    @9
    @23
    @3
    wph
    simprl1
    wph
    @5
    @11
    wss
    #
    @26
    wph
    @17
    cN
    cA
    cuz
    cfv
    wcel
    @28
    erdszelem.a
    cA
    c1
    cN
    elfzuz3
    cA
    c1
    cN
    fzss2
    3syl
    adantr
    sstrd
    vs
    @11
    selpw
    sylibr
    @27
    cR
    @2
    @1
    cle
    wph
    cR
    @2
    cle
    wbr
    #
    @26
    wph
    @29
    @2
    cR
    clt
    wbr
    #
    wn
    wph
    @2
    c1
    cR
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @30
    erdszelem7.m
    wph
    @32
    @2
    @31
    cle
    wbr
    #
    @30
    wph
    @2
    c1
    cuz
    cfv
    #
    wcel
    @31
    cz
    wcel
    #
    @32
    @33
    wb
    wph
    @2
    cn
    @34
    wph
    @11
    cn
    cA
    cK
    wph
    vx
    vy
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem.o
    erdszelem6
    erdszelem.a
    ffvelrnd
    #
    nnuz
    syl6eleq
    wph
    cR
    cn
    wcel
    #
    cR
    cz
    wcel
    @35
    erdszelem7.r
    cR
    nnz
    cR
    peano2zm
    3syl
    @2
    c1
    @31
    elfz5
    syl2anc
    wph
    @2
    cn
    wcel
    @37
    @30
    @33
    wb
    @36
    erdszelem7.r
    @2
    cR
    nnltlem1
    syl2anc
    bitr4d
    mtbid
    wph
    cR
    @2
    wph
    cR
    erdszelem7.r
    nnred
    wph
    @14
    cr
    @2
    @14
    cn
    cr
    @14
    cfn
    wcel
    @14
    cn
    wss
    vy
    cA
    @6
    cF
    cO
    @25
    erdszelem2
    simpri
    nnssre
    sstri
    @18
    sseldi
    lenltd
    mpbird
    adantr
    wph
    @24
    @3
    simprr
    breqtrrd
    @22
    @9
    @23
    @3
    wph
    simprl2
    jca32
    expr
    sylan2b
    expimpd
    reximdv2
    mpd
end
