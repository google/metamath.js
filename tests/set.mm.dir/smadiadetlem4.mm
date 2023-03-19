include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "ccom.mm"
include "cif.mm"
include "co.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "csn.mm"
include "cdif.mm"
include "ccmn.mm"
include "cfn.mm"
include "cbs.mm"
include "wral.mm"
include "ccrg.mm"
include "crngmgp.mm"
include "mp1i.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "jca.mm"
include "simprl.mm"
include "simprr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eqid.mm"
include "matecl.mm"
include "syl3anc.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "ralrimivva.mm"
include "crg.mm"
include "crngring.mm"
include "ring0cl.mm"
include "mp2b.mm"
include "eleqtri.mm"
include "jctir.mm"
include "simpr.mm"
include "ringidval.mm"
include "gsummatr01.mm"
include "syl113anc.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "smadiadetlem3.mm"
include "eqtrd.mm"

theorem smadiadetlem4
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
  disjoint G i
  disjoint G j
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
  assert |- ( ( M e. B /\ K e. N ) -> ( R gsum ( p e. { q e. P | ( q ` K ) = K } |-> ( ( ( Y o. S ) ` p ) ( .r ` R ) ( G gsum ( n e. N |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = K , .1. , .0. ) , ( i M j ) ) ) ( p ` n ) ) ) ) ) ) ) = ( R gsum ( p e. W |-> ( ( ( Y o. Z ) ` p ) ( .r ` R ) ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { K } ) |-> ( i M j ) ) ( p ` n ) ) ) ) ) ) ) )

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
    cK
    vq
    cv
    cfv
    cK
    wceq
    vq
    cP
    crab
    #
    vp
    cv
    #
    cY
    cS
    ccom
    cfv
    #
    cG
    vn
    cN
    vn
    cv
    #
    @6
    @4
    cfv
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cK
    wceq
    vj
    cv
    #
    cK
    wceq
    c.1
    c.0
    cif
    @8
    @9
    cM
    co
    #
    cif
    cmpt2
    co
    cmpt
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
    vp
    @3
    @5
    cG
    vn
    cN
    cK
    csn
    cdif
    #
    @6
    @7
    vi
    vj
    @15
    @15
    @10
    cmpt2
    co
    cmpt
    cgsu
    co
    #
    @12
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vp
    cW
    @4
    cY
    cZ
    ccom
    cfv
    @16
    @12
    co
    cmpt
    cgsu
    co
    @2
    @14
    @18
    cR
    cgsu
    @2
    vp
    @3
    @13
    @17
    @2
    @4
    @3
    wcel
    #
    wa
    #
    @11
    @16
    @5
    @12
    @20
    cG
    ccmn
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    @10
    cG
    cbs
    cfv
    #
    wcel
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    c.0
    @24
    wcel
    #
    wa
    @1
    @1
    @19
    @11
    @16
    wceq
    @2
    @23
    @19
    @2
    @21
    @22
    cR
    ccrg
    wcel
    #
    @21
    @2
    marep01ma.r
    cR
    cG
    smadiadetlem.g
    crngmgp
    mp1i
    @0
    @22
    @1
    @0
    @22
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
    adantr
    jca
    adantr
    @20
    @26
    @27
    @2
    @26
    @19
    @2
    @25
    vi
    vj
    cN
    cN
    @2
    @8
    cN
    wcel
    #
    @9
    cN
    wcel
    #
    wa
    #
    wa
    #
    @10
    cR
    cbs
    cfv
    #
    @24
    @32
    @29
    @30
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @10
    @33
    wcel
    @2
    @29
    @30
    simprl
    @2
    @29
    @30
    simprr
    @2
    @35
    @31
    @0
    @35
    @1
    @0
    @35
    cB
    @34
    cM
    marep01ma.b
    eleq2i
    biimpi
    adantr
    adantr
    cA
    cR
    @8
    @9
    @33
    cM
    cN
    marep01ma.a
    @33
    eqid
    #
    matecl
    syl3anc
    @33
    cR
    cG
    smadiadetlem.g
    @36
    mgpbas
    #
    syl6eleq
    ralrimivva
    adantr
    c.0
    @33
    @24
    @28
    cR
    crg
    wcel
    c.0
    @33
    wcel
    marep01ma.r
    cR
    crngring
    @33
    cR
    c.0
    @36
    marep01ma.0
    ring0cl
    mp2b
    @37
    eleqtri
    jctir
    @2
    @1
    @19
    @0
    @1
    simpr
    adantr
    #
    @38
    @2
    @19
    simpr
    cM
    c.0
    cP
    @4
    @3
    @24
    vi
    vj
    vn
    cG
    cK
    cK
    cN
    c.1
    vq
    smadiadetlem.p
    @3
    eqid
    cR
    c.1
    cG
    smadiadetlem.g
    marep01ma.1
    ringidval
    @24
    eqid
    gsummatr01
    syl113anc
    oveq2d
    mpteq2dva
    oveq2d
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
    vq
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
    smadiadetlem3
    eqtrd
end
