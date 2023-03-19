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
include "ringacl.mm"
include "syl3anc.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "csn.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "cfn.mm"
include "snex.mm"
include "a1i.mm"
include "wss.mm"
include "snssd.mm"
include "simp2.mm"
include "sseldd.mm"
include "syld3an2.mm"
include "eqidd.mm"
include "offval22.mm"
include "eqcomd.mm"
include "mpt2snif.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "cdif.mm"
include "wn.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "3ad2ant2.mm"
include "mpt2eq3dva.mm"
include "difss.mm"
include "mp2an.mm"
include "mdetrlin.mm"

theorem mdetrlin2
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mdetrlin2.d: |- D = ( N maDet R )
  assume mdetrlin2.k: |- K = ( Base ` R )
  assume mdetrlin2.p: |- .+ = ( +g ` R )
  assume mdetrlin2.r: |- ( ph -> R e. CRing )
  assume mdetrlin2.n: |- ( ph -> N e. Fin )
  assume mdetrlin2.x: |- ( ( ph /\ i e. N /\ j e. N ) -> X e. K )
  assume mdetrlin2.y: |- ( ( ph /\ i e. N /\ j e. N ) -> Y e. K )
  assume mdetrlin2.z: |- ( ( ph /\ i e. N /\ j e. N ) -> Z e. K )
  assume mdetrlin2.i: |- ( ph -> I e. N )

  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint K i
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint I i
  disjoint I j
  disjoint .+ i
  disjoint .+ j
  assert |- ( ph -> ( D ` ( i e. N , j e. N |-> if ( i = I , ( X .+ Y ) , Z ) ) ) = ( ( D ` ( i e. N , j e. N |-> if ( i = I , X , Z ) ) ) .+ ( D ` ( i e. N , j e. N |-> if ( i = I , Y , Z ) ) ) ) )

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
    c.pl
    cR
    cI
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
    cX
    cY
    c.pl
    co
    #
    cZ
    cif
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @3
    cX
    cZ
    cif
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    @3
    cY
    cZ
    cif
    #
    cmpt2
    #
    mdetrlin2.d
    @0
    eqid
    #
    @1
    eqid
    #
    mdetrlin2.p
    mdetrlin2.r
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
    @11
    mdetrlin2.k
    @12
    mdetrlin2.n
    mdetrlin2.r
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
    cZ
    cK
    @15
    cR
    crg
    wcel
    #
    cX
    cK
    wcel
    #
    cY
    cK
    wcel
    #
    @4
    cK
    wcel
    wph
    @13
    @16
    @14
    wph
    cR
    ccrg
    wcel
    @16
    mdetrlin2.r
    cR
    crngring
    syl
    3ad2ant1
    mdetrlin2.x
    mdetrlin2.y
    cK
    c.pl
    cR
    cX
    cY
    mdetrlin2.k
    mdetrlin2.p
    ringacl
    syl3anc
    mdetrlin2.z
    ifcld
    matbas2d
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
    @11
    mdetrlin2.k
    @12
    mdetrlin2.n
    mdetrlin2.r
    @15
    @3
    cX
    cZ
    cK
    mdetrlin2.x
    mdetrlin2.z
    ifcld
    matbas2d
    wph
    vi
    vj
    @0
    @1
    @9
    cR
    cK
    cN
    ccrg
    @11
    mdetrlin2.k
    @12
    mdetrlin2.n
    mdetrlin2.r
    @15
    @3
    cY
    cZ
    cK
    mdetrlin2.y
    mdetrlin2.z
    ifcld
    matbas2d
    mdetrlin2.i
    wph
    vi
    vj
    cI
    csn
    #
    cN
    @5
    cmpt2
    #
    vi
    vj
    @19
    cN
    @7
    cmpt2
    #
    vi
    vj
    @19
    cN
    @9
    cmpt2
    #
    c.pl
    cof
    #
    co
    #
    @6
    @19
    cN
    cxp
    #
    cres
    #
    @8
    @25
    cres
    #
    @10
    @25
    cres
    #
    @23
    co
    wph
    vi
    vj
    @19
    cN
    @4
    cmpt2
    #
    vi
    vj
    @19
    cN
    cX
    cmpt2
    #
    vi
    vj
    @19
    cN
    cY
    cmpt2
    #
    @23
    co
    #
    @20
    @24
    wph
    @32
    @29
    wph
    vi
    vj
    @19
    cN
    cX
    cY
    c.pl
    @30
    @31
    cvv
    cfn
    cK
    cK
    @19
    cvv
    wcel
    wph
    cI
    snex
    a1i
    mdetrlin2.n
    wph
    @13
    @2
    @19
    wcel
    #
    @14
    @17
    wph
    @33
    @14
    w3a
    @19
    cN
    @2
    wph
    @33
    @19
    cN
    wss
    #
    @14
    wph
    cI
    cN
    mdetrlin2.i
    snssd
    #
    3ad2ant1
    wph
    @33
    @14
    simp2
    sseldd
    #
    mdetrlin2.x
    syld3an2
    wph
    @13
    @33
    @14
    @18
    @36
    mdetrlin2.y
    syld3an2
    wph
    @30
    eqidd
    wph
    @31
    eqidd
    offval22
    eqcomd
    cN
    @4
    cZ
    vi
    vj
    cI
    mpt2snif
    @21
    @30
    @22
    @31
    @23
    cN
    cX
    cZ
    vi
    vj
    cI
    mpt2snif
    cN
    cY
    cZ
    vi
    vj
    cI
    mpt2snif
    oveq12i
    3eqtr4g
    wph
    @34
    cN
    cN
    wss
    #
    @26
    @20
    wceq
    @35
    cN
    ssid
    #
    vi
    vj
    cN
    cN
    @19
    cN
    @5
    resmpt2
    sylancl
    wph
    @27
    @21
    @28
    @22
    @23
    wph
    @34
    @37
    @27
    @21
    wceq
    @35
    @38
    vi
    vj
    cN
    cN
    @19
    cN
    @7
    resmpt2
    sylancl
    wph
    @34
    @37
    @28
    @22
    wceq
    @35
    @38
    vi
    vj
    cN
    cN
    @19
    cN
    @9
    resmpt2
    sylancl
    oveq12d
    3eqtr4d
    wph
    vi
    vj
    cN
    @19
    cdif
    #
    cN
    @5
    cmpt2
    #
    vi
    vj
    @39
    cN
    @7
    cmpt2
    #
    @6
    @39
    cN
    cxp
    #
    cres
    #
    @8
    @42
    cres
    #
    wph
    vi
    vj
    @39
    cN
    @5
    @7
    @2
    @39
    wcel
    #
    wph
    @5
    @7
    wceq
    #
    @14
    @45
    @3
    wn
    #
    @46
    @45
    @2
    cI
    @2
    cN
    cI
    eldifsni
    neneqd
    #
    @47
    @5
    cZ
    @7
    @3
    @4
    cZ
    iffalse
    #
    @3
    cX
    cZ
    iffalse
    eqtr4d
    syl
    3ad2ant2
    mpt2eq3dva
    @39
    cN
    wss
    #
    @37
    @43
    @40
    wceq
    cN
    @19
    difss
    #
    @38
    vi
    vj
    cN
    cN
    @39
    cN
    @5
    resmpt2
    mp2an
    #
    @50
    @37
    @44
    @41
    wceq
    @51
    @38
    vi
    vj
    cN
    cN
    @39
    cN
    @7
    resmpt2
    mp2an
    3eqtr4g
    wph
    @40
    vi
    vj
    @39
    cN
    @9
    cmpt2
    #
    @43
    @10
    @42
    cres
    #
    wph
    vi
    vj
    @39
    cN
    @5
    @9
    @45
    wph
    @5
    @9
    wceq
    #
    @14
    @45
    @47
    @55
    @48
    @47
    @5
    cZ
    @9
    @49
    @3
    cY
    cZ
    iffalse
    eqtr4d
    syl
    3ad2ant2
    mpt2eq3dva
    @52
    @50
    @37
    @54
    @53
    wceq
    @51
    @38
    vi
    vj
    cN
    cN
    @39
    cN
    @9
    resmpt2
    mp2an
    3eqtr4g
    mdetrlin
end
