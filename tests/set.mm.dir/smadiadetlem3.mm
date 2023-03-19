include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "wceq.mm"
include "crab.mm"
include "cres.mm"
include "cbs.mm"
include "cvv.mm"
include "ccntz.mm"
include "eqid.mm"
include "cmnd.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "ringmnd.mm"
include "mp2b.mm"
include "a1i.mm"
include "csymg.mm"
include "fvexd.mm"
include "syl5eqel.mm"
include "smadiadetlem3lem1.mm"
include "smadiadetlem3lem2.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "diffi.mm"
include "symgbasfi.mm"
include "3syl.mm"
include "ovexd.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fsuppmptdm.mm"
include "wf1o.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "symgfixf1o.mm"
include "sylan.mm"
include "gsumzf1o.mm"
include "symgfixelsi.mm"
include "adantll.mm"
include "eqidd.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "mpteq2dva.mm"
include "fmptco.mm"
include "wi.mm"
include "zrhcopsgndif.mm"
include "imp.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eqtr2d.mm"

theorem smadiadetlem3
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let cL: class L
  let cQ: class Q
  let vy: setvar y
  assume marep01ma.a: |- A = ( N Mat R )
  assume marep01ma.b: |- B = ( Base ` A )
  assume marep01ma.r: |- R e. CRing
  assume marep01ma.0: |- .0. = ( 0g ` R )
  assume marep01ma.1: |- .1. = ( 1r ` R )
  assume smadiadetlem.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume smadiadetlem.g: |- G = ( mulGrp ` R )
  assume madetminlem.y: |- Y = ( ZRHom ` R )
  assume madetminlem.s: |- S = ( pmSgn ` N )
  assume madetminlem.t: |- .x. = ( .r ` R )
  assume smadiadetlem.w: |- W = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume smadiadetlem.z: |- Z = ( pmSgn ` ( N \ { K } ) )

  disjoint i j
  disjoint i n
  disjoint B i
  disjoint j n
  disjoint B j
  disjoint B n
  disjoint i q
  disjoint K i
  disjoint j q
  disjoint K j
  disjoint n q
  disjoint K n
  disjoint K q
  disjoint M i
  disjoint M j
  disjoint M n
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint P i
  disjoint P j
  disjoint P n
  disjoint P q
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint .1. i
  disjoint .1. j
  disjoint .1. n
  disjoint .0. i
  disjoint .0. j
  disjoint .0. n
  disjoint G n
  disjoint n p
  disjoint B p
  disjoint K p
  disjoint M p
  disjoint N p
  disjoint P p
  disjoint R p
  disjoint i p
  disjoint j p
  disjoint p q
  disjoint W n
  disjoint W p
  disjoint G p
  disjoint Y p
  disjoint Z p
  disjoint k l
  disjoint B k
  disjoint B l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  disjoint i m
  disjoint j m
  disjoint m n
  disjoint B m
  disjoint m q
  disjoint K m
  disjoint L i
  disjoint L j
  disjoint L m
  disjoint L n
  disjoint L q
  disjoint M m
  disjoint N m
  disjoint P m
  disjoint Q i
  disjoint Q j
  disjoint Q m
  disjoint Q n
  disjoint Q q
  disjoint R m
  disjoint .1. m
  disjoint .0. m
  disjoint G m
  disjoint L p
  disjoint G y
  disjoint p y
  disjoint K y
  disjoint i y
  disjoint j y
  disjoint n y
  disjoint M y
  disjoint N y
  disjoint R y
  disjoint W y
  disjoint Y y
  disjoint Z y
  assert |- ( ( M e. B /\ K e. N ) -> ( R gsum ( p e. { q e. P | ( q ` K ) = K } |-> ( ( ( Y o. S ) ` p ) ( .r ` R ) ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { K } ) |-> ( i M j ) ) ( p ` n ) ) ) ) ) ) ) = ( R gsum ( p e. W |-> ( ( ( Y o. Z ) ` p ) ( .r ` R ) ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { K } ) |-> ( i M j ) ) ( p ` n ) ) ) ) ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cR
    vp
    cW
    vp
    cv
    #
    cY
    cZ
    ccom
    #
    cfv
    #
    cG
    vn
    cN
    cK
    csn
    #
    cdif
    #
    vn
    cv
    #
    @8
    @3
    cfv
    #
    vi
    vj
    @7
    @7
    vi
    cv
    vj
    cv
    cM
    co
    cmpt2
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    @16
    vp
    cK
    vq
    cv
    #
    cfv
    #
    cK
    wceq
    #
    vq
    cP
    crab
    #
    @3
    @7
    cres
    #
    cmpt
    #
    ccom
    #
    cgsu
    co
    cR
    vp
    @20
    @3
    cY
    cS
    ccom
    cfv
    #
    @13
    @14
    co
    #
    cmpt
    #
    cgsu
    co
    @2
    cW
    cR
    cbs
    cfv
    #
    @20
    @16
    cR
    @22
    cvv
    c.0
    cR
    ccntz
    cfv
    #
    @27
    eqid
    marep01ma.0
    @28
    eqid
    cR
    cmnd
    wcel
    #
    @2
    cR
    ccrg
    wcel
    cR
    crg
    wcel
    @29
    marep01ma.r
    cR
    crngring
    cR
    ringmnd
    mp2b
    a1i
    @2
    cW
    @7
    csymg
    cfv
    #
    cbs
    cfv
    #
    cvv
    smadiadetlem.w
    @2
    @30
    cbs
    fvexd
    syl5eqel
    cA
    cB
    cP
    cR
    cS
    c.x
    c.1
    vi
    vj
    vn
    cG
    cK
    cM
    cN
    cW
    cY
    c.0
    cZ
    vp
    marep01ma.a
    marep01ma.b
    marep01ma.r
    marep01ma.0
    marep01ma.1
    smadiadetlem.p
    smadiadetlem.g
    madetminlem.y
    madetminlem.s
    madetminlem.t
    smadiadetlem.w
    smadiadetlem.z
    smadiadetlem3lem1
    cA
    cB
    cP
    cR
    cS
    c.x
    c.1
    vi
    vj
    vn
    cG
    cK
    cM
    cN
    cW
    cY
    c.0
    cZ
    vp
    marep01ma.a
    marep01ma.b
    marep01ma.r
    marep01ma.0
    marep01ma.1
    smadiadetlem.p
    smadiadetlem.g
    madetminlem.y
    madetminlem.s
    madetminlem.t
    smadiadetlem.w
    smadiadetlem.z
    smadiadetlem3lem2
    @2
    vp
    cW
    @16
    cvv
    cvv
    @15
    c.0
    @16
    eqid
    @2
    cW
    @31
    cfn
    smadiadetlem.w
    @2
    cN
    cfn
    wcel
    #
    @7
    cfn
    wcel
    @31
    cfn
    wcel
    @0
    @32
    @1
    @0
    @32
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marep01ma.a
    marep01ma.b
    matrcl
    simpld
    #
    adantr
    cN
    @6
    diffi
    @7
    @31
    @30
    @30
    eqid
    @31
    eqid
    symgbasfi
    3syl
    syl5eqel
    @2
    @3
    cW
    wcel
    wa
    @5
    @13
    @14
    ovexd
    c.0
    cvv
    wcel
    @2
    c.0
    cR
    c0g
    cfv
    cvv
    marep01ma.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fsuppmptdm
    @0
    @32
    @1
    @20
    cW
    @22
    wf1o
    @33
    cP
    @20
    cW
    @22
    cK
    cN
    cfn
    vp
    smadiadetlem.p
    @19
    cK
    @3
    cfv
    #
    cK
    wceq
    vq
    vp
    cP
    @17
    @3
    wceq
    @18
    @34
    cK
    cK
    @17
    @3
    fveq1
    eqeq1d
    cbvrabv
    smadiadetlem.w
    @22
    eqid
    symgfixf1o
    sylan
    gsumzf1o
    @2
    @23
    @26
    cR
    cgsu
    @2
    @23
    vp
    @20
    @21
    @4
    cfv
    #
    @13
    @14
    co
    #
    cmpt
    @26
    @2
    vp
    vy
    @20
    cW
    @21
    vy
    cv
    #
    @4
    cfv
    #
    cG
    vn
    @7
    @8
    @8
    @37
    cfv
    #
    @10
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @14
    co
    #
    @36
    @22
    @16
    @1
    @3
    @20
    wcel
    #
    @21
    cW
    wcel
    @0
    @7
    cP
    @20
    cW
    @3
    cK
    cN
    vq
    smadiadetlem.p
    @20
    eqid
    smadiadetlem.w
    @7
    eqid
    symgfixelsi
    adantll
    @2
    @22
    eqidd
    @16
    vy
    cW
    @43
    cmpt
    wceq
    @2
    vp
    vy
    cW
    @15
    @43
    @3
    @37
    wceq
    #
    @5
    @38
    @13
    @42
    @14
    @3
    @37
    @4
    fveq2
    @45
    @12
    @41
    cG
    cgsu
    @45
    vn
    @7
    @11
    @40
    @45
    @9
    @39
    @8
    @10
    @8
    @3
    @37
    fveq1
    oveq2d
    mpteq2dv
    oveq2d
    oveq12d
    cbvmptv
    a1i
    @37
    @21
    wceq
    #
    @38
    @35
    @42
    @13
    @14
    @37
    @21
    @4
    fveq2
    @46
    @41
    @12
    cG
    cgsu
    @46
    vn
    @7
    @40
    @11
    @46
    @8
    @7
    wcel
    #
    wa
    @39
    @9
    @8
    @10
    @46
    @47
    @39
    @8
    @21
    cfv
    @9
    @8
    @37
    @21
    fveq1
    @8
    @7
    @3
    fvres
    sylan9eq
    oveq2d
    mpteq2dva
    oveq2d
    oveq12d
    fmptco
    @2
    vp
    @20
    @36
    @25
    @2
    @44
    wa
    @35
    @24
    @13
    @14
    @2
    @44
    @35
    @24
    wceq
    #
    @0
    @32
    @1
    @44
    @48
    wi
    @33
    cP
    @3
    cR
    cS
    cK
    cN
    cY
    cZ
    vq
    smadiadetlem.p
    madetminlem.s
    smadiadetlem.z
    madetminlem.y
    zrhcopsgndif
    sylan
    imp
    oveq1d
    mpteq2dva
    eqtrd
    oveq2d
    eqtr2d
end
