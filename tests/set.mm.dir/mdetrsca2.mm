include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cres.mm"
include "cvv.mm"
include "cfn.mm"
include "snex.mm"
include "a1i.mm"
include "snssd.mm"
include "sselda.mm"
include "3adant3.mm"
include "syld3an2.mm"
include "fconstmpt2.mm"
include "eqidd.mm"
include "offval22.mm"
include "mpt2snif.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "wss.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "cdif.mm"
include "wn.mm"
include "wne.mm"
include "eldifsni.mm"
include "3ad2ant2.mm"
include "neneqd.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "mpt2eq3dva.mm"
include "difss.mm"
include "mp2an.mm"
include "mdetrsca.mm"

theorem mdetrsca2
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cI: class I
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  assume mdetrsca2.d: |- D = ( N maDet R )
  assume mdetrsca2.k: |- K = ( Base ` R )
  assume mdetrsca2.t: |- .x. = ( .r ` R )
  assume mdetrsca2.r: |- ( ph -> R e. CRing )
  assume mdetrsca2.n: |- ( ph -> N e. Fin )
  assume mdetrsca2.x: |- ( ( ph /\ i e. N /\ j e. N ) -> X e. K )
  assume mdetrsca2.y: |- ( ( ph /\ i e. N /\ j e. N ) -> Y e. K )
  assume mdetrsca2.f: |- ( ph -> F e. K )
  assume mdetrsca2.i: |- ( ph -> I e. N )

  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint F i
  disjoint F j
  disjoint K i
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint I i
  disjoint I j
  disjoint .x. i
  disjoint .x. j
  assert |- ( ph -> ( D ` ( i e. N , j e. N |-> if ( i = I , ( F .x. X ) , Y ) ) ) = ( F .x. ( D ` ( i e. N , j e. N |-> if ( i = I , X , Y ) ) ) ) )

  proof
    wph
    cN
    cR
    cmat
    co
    #
    @0
    cbs
    cfv
    #
    cD
    cR
    c.x
    cI
    cK
    cN
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cI
    wceq
    #
    cF
    cX
    c.x
    co
    #
    cY
    cif
    #
    cmpt2
    #
    cF
    vi
    vj
    cN
    cN
    @3
    cX
    cY
    cif
    #
    cmpt2
    #
    mdetrsca2.d
    @0
    eqid
    #
    @1
    eqid
    #
    mdetrsca2.k
    mdetrsca2.t
    mdetrsca2.r
    wph
    vi
    vj
    @0
    @1
    @5
    cR
    cK
    cN
    ccrg
    @9
    mdetrsca2.k
    @10
    mdetrsca2.n
    mdetrsca2.r
    wph
    @2
    cN
    wcel
    #
    vj
    cv
    cN
    wcel
    #
    w3a
    #
    @3
    @4
    cY
    cK
    @13
    cR
    crg
    wcel
    #
    cF
    cK
    wcel
    #
    cX
    cK
    wcel
    #
    @4
    cK
    wcel
    wph
    @11
    @14
    @12
    wph
    cR
    ccrg
    wcel
    @14
    mdetrsca2.r
    cR
    crngring
    syl
    3ad2ant1
    wph
    @11
    @15
    @12
    mdetrsca2.f
    3ad2ant1
    mdetrsca2.x
    cK
    cR
    c.x
    cF
    cX
    mdetrsca2.k
    mdetrsca2.t
    ringcl
    syl3anc
    mdetrsca2.y
    ifcld
    matbas2d
    mdetrsca2.f
    wph
    vi
    vj
    @0
    @1
    @7
    cR
    cK
    cN
    ccrg
    @9
    mdetrsca2.k
    @10
    mdetrsca2.n
    mdetrsca2.r
    @13
    @3
    cX
    cY
    cK
    mdetrsca2.x
    mdetrsca2.y
    ifcld
    matbas2d
    mdetrsca2.i
    wph
    cI
    csn
    #
    cN
    cxp
    #
    cF
    csn
    cxp
    #
    vi
    vj
    @17
    cN
    @7
    cmpt2
    #
    c.x
    cof
    #
    co
    #
    vi
    vj
    @17
    cN
    @5
    cmpt2
    #
    @19
    @8
    @18
    cres
    #
    @21
    co
    @6
    @18
    cres
    #
    wph
    @19
    vi
    vj
    @17
    cN
    cX
    cmpt2
    #
    @21
    co
    vi
    vj
    @17
    cN
    @4
    cmpt2
    @22
    @23
    wph
    vi
    vj
    @17
    cN
    cF
    cX
    c.x
    @19
    @26
    cvv
    cfn
    cK
    cK
    @17
    cvv
    wcel
    wph
    cI
    snex
    a1i
    mdetrsca2.n
    wph
    @2
    @17
    wcel
    #
    @15
    @12
    mdetrsca2.f
    3ad2ant1
    wph
    @11
    @27
    @12
    @16
    wph
    @27
    @11
    @12
    wph
    @17
    cN
    @2
    wph
    cI
    cN
    mdetrsca2.i
    snssd
    #
    sselda
    3adant3
    mdetrsca2.x
    syld3an2
    @19
    vi
    vj
    @17
    cN
    cF
    cmpt2
    wceq
    wph
    vi
    vj
    @17
    cN
    cF
    fconstmpt2
    a1i
    wph
    @26
    eqidd
    offval22
    @20
    @26
    @19
    @21
    cN
    cX
    cY
    vi
    vj
    cI
    mpt2snif
    oveq2i
    cN
    @4
    cY
    vi
    vj
    cI
    mpt2snif
    3eqtr4g
    wph
    @24
    @20
    @19
    @21
    wph
    @17
    cN
    wss
    #
    cN
    cN
    wss
    #
    @24
    @20
    wceq
    @28
    cN
    ssid
    #
    vi
    vj
    cN
    cN
    @17
    cN
    @7
    resmpt2
    sylancl
    oveq2d
    wph
    @29
    @30
    @25
    @23
    wceq
    @28
    @31
    vi
    vj
    cN
    cN
    @17
    cN
    @5
    resmpt2
    sylancl
    3eqtr4rd
    wph
    vi
    vj
    cN
    @17
    cdif
    #
    cN
    @5
    cmpt2
    #
    vi
    vj
    @32
    cN
    @7
    cmpt2
    #
    @6
    @32
    cN
    cxp
    #
    cres
    #
    @8
    @35
    cres
    #
    wph
    vi
    vj
    @32
    cN
    @5
    @7
    wph
    @2
    @32
    wcel
    #
    @12
    w3a
    #
    @3
    wn
    #
    @5
    @7
    wceq
    @39
    @2
    cI
    @38
    wph
    @2
    cI
    wne
    @12
    @2
    cN
    cI
    eldifsni
    3ad2ant2
    neneqd
    @40
    @5
    cY
    @7
    @3
    @4
    cY
    iffalse
    @3
    cX
    cY
    iffalse
    eqtr4d
    syl
    mpt2eq3dva
    @32
    cN
    wss
    #
    @30
    @36
    @33
    wceq
    cN
    @17
    difss
    #
    @31
    vi
    vj
    cN
    cN
    @32
    cN
    @5
    resmpt2
    mp2an
    @41
    @30
    @37
    @34
    wceq
    @42
    @31
    vi
    vj
    cN
    cN
    @32
    cN
    @7
    resmpt2
    mp2an
    3eqtr4g
    mdetrsca
end
