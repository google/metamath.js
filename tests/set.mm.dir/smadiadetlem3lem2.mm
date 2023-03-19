include "wcel.mm"
include "wa.mm"
include "ccmn.mm"
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
include "crn.mm"
include "cbs.mm"
include "wss.mm"
include "ccntz.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "ringcmn.mm"
include "mp2b.mm"
include "wral.mm"
include "smadiadetlem3lem0.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "cntzcmnss.mm"
include "sylancr.mm"

theorem smadiadetlem3lem2
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
  let vp: setvar p
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let vq: setvar q
  let cL: class L
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
  assume smadiadetlem.w: |- W = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume smadiadetlem.z: |- Z = ( pmSgn ` ( N \ { K } ) )

  disjoint i j
  disjoint i n
  disjoint B i
  disjoint j n
  disjoint B j
  disjoint B n
  disjoint K i
  disjoint K j
  disjoint K n
  disjoint M i
  disjoint M j
  disjoint M n
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint P i
  disjoint P j
  disjoint P n
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
  disjoint W n
  disjoint W p
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
  disjoint i q
  disjoint j q
  disjoint m q
  disjoint K m
  disjoint n q
  disjoint K q
  disjoint L i
  disjoint L j
  disjoint L m
  disjoint L n
  disjoint L q
  disjoint M m
  disjoint N m
  disjoint P m
  disjoint P q
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
  disjoint p q
  assert |- ( ( M e. B /\ K e. N ) -> ran ( p e. W |-> ( ( ( Y o. Z ) ` p ) ( .r ` R ) ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { K } ) |-> ( i M j ) ) ( p ` n ) ) ) ) ) ) C_ ( ( Cntz ` R ) ` ran ( p e. W |-> ( ( ( Y o. Z ) ` p ) ( .r ` R ) ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { K } ) |-> ( i M j ) ) ( p ` n ) ) ) ) ) ) ) )

  proof
    cM
    cB
    wcel
    cK
    cN
    wcel
    wa
    #
    cR
    ccmn
    wcel
    #
    vp
    cW
    vp
    cv
    #
    cY
    cZ
    ccom
    cfv
    cG
    vn
    cN
    cK
    csn
    cdif
    #
    vn
    cv
    #
    @4
    @2
    cfv
    vi
    vj
    @3
    @3
    vi
    cv
    vj
    cv
    cM
    co
    cmpt2
    co
    cmpt
    cgsu
    co
    cR
    cmulr
    cfv
    co
    #
    cmpt
    #
    crn
    #
    cR
    cbs
    cfv
    #
    wss
    #
    @7
    @7
    cR
    ccntz
    cfv
    #
    cfv
    wss
    cR
    ccrg
    wcel
    cR
    crg
    wcel
    @1
    marep01ma.r
    cR
    crngring
    cR
    ringcmn
    mp2b
    @0
    @5
    @8
    wcel
    #
    vp
    cW
    wral
    @9
    @0
    @11
    vp
    cW
    cA
    cB
    cP
    @2
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
    smadiadetlem3lem0
    ralrimiva
    vp
    cW
    @5
    @8
    @6
    @6
    eqid
    rnmptss
    syl
    @8
    @7
    cR
    @10
    @8
    eqid
    @10
    eqid
    cntzcmnss
    sylancr
end
