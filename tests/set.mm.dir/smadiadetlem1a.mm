include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cdif.mm"
include "ccom.mm"
include "cif.mm"
include "co.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wa.mm"
include "smadiadetlem0.mm"
include "imp.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "crg.mm"
include "cbs.mm"
include "ccrg.mm"
include "crngring.mm"
include "mp1i.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "zrhcopsgnelbas.mm"
include "syl3anc.mm"
include "eqid.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "mp2b.mm"
include "csymg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "gsumz.mm"
include "sylancr.mm"
include "3eqtrd.mm"

theorem smadiadetlem1a
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
  let cL: class L
  let cM: class M
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let cQ: class Q
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
  disjoint L i
  disjoint L j
  disjoint L n
  disjoint L q
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
  disjoint L p
  disjoint M p
  disjoint N p
  disjoint P p
  disjoint R p
  disjoint i p
  disjoint j p
  disjoint p q
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
  disjoint L m
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
  assert |- ( ( M e. B /\ K e. N /\ L e. N ) -> ( R gsum ( p e. ( P \ { q e. P | ( q ` K ) = L } ) |-> ( ( ( Y o. S ) ` p ) .x. ( G gsum ( n e. N |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = L , .1. , .0. ) , ( i M j ) ) ) ( p ` n ) ) ) ) ) ) ) = .0. )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    cL
    cN
    wcel
    #
    w3a
    #
    cR
    vp
    cP
    cK
    vq
    cv
    cfv
    cL
    wceq
    vq
    cP
    crab
    #
    cdif
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
    @8
    @6
    cfv
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
    cL
    wceq
    c.1
    c.0
    cif
    @9
    @10
    cM
    co
    cif
    cmpt2
    co
    cmpt
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vp
    @5
    @7
    c.0
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vp
    @5
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @3
    @13
    @15
    cR
    cgsu
    @3
    vp
    @5
    @12
    @14
    @3
    @6
    @5
    wcel
    #
    wa
    #
    @11
    c.0
    @7
    c.x
    @3
    @18
    @11
    c.0
    wceq
    cA
    cB
    cP
    @6
    cR
    c.1
    vi
    vj
    vn
    cG
    cK
    cL
    cM
    cN
    c.0
    vq
    marep01ma.a
    marep01ma.b
    marep01ma.r
    marep01ma.0
    marep01ma.1
    smadiadetlem.p
    smadiadetlem.g
    smadiadetlem0
    imp
    oveq2d
    mpteq2dva
    oveq2d
    @3
    @15
    @16
    cR
    cgsu
    @3
    vp
    @5
    @14
    c.0
    @19
    cR
    crg
    wcel
    #
    @7
    cR
    cbs
    cfv
    #
    wcel
    #
    @14
    c.0
    wceq
    cR
    ccrg
    wcel
    #
    @20
    @19
    marep01ma.r
    cR
    crngring
    #
    mp1i
    #
    @19
    @20
    cN
    cfn
    wcel
    #
    @6
    cP
    wcel
    #
    @22
    @25
    @3
    @26
    @18
    @0
    @1
    @26
    @2
    @0
    @26
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
    3ad2ant1
    adantr
    @18
    @27
    @3
    @6
    cP
    @4
    eldifi
    adantl
    cP
    @6
    cR
    cS
    cN
    cY
    smadiadetlem.p
    madetminlem.s
    madetminlem.y
    zrhcopsgnelbas
    syl3anc
    @21
    cR
    c.x
    @7
    c.0
    @21
    eqid
    madetminlem.t
    marep01ma.0
    ringrz
    syl2anc
    mpteq2dva
    oveq2d
    @3
    cR
    cmnd
    wcel
    #
    @5
    cvv
    wcel
    #
    @17
    c.0
    wceq
    @23
    @20
    @28
    marep01ma.r
    @24
    cR
    ringmnd
    mp2b
    cP
    cvv
    wcel
    @29
    @3
    cP
    cN
    csymg
    cfv
    #
    cbs
    cfv
    cvv
    smadiadetlem.p
    @30
    cbs
    fvex
    eqeltri
    cP
    @4
    cvv
    difexg
    mp1i
    @5
    vp
    cR
    cvv
    c.0
    marep01ma.0
    gsumz
    sylancr
    3eqtrd
end
