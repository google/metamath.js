include "wcel.mm"
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
include "smadiadetlem1a.mm"
include "3anidm23.mm"

theorem smadiadetlem2
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
  let cY: class Y
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
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
  assert |- ( ( M e. B /\ K e. N ) -> ( R gsum ( p e. ( P \ { q e. P | ( q ` K ) = K } ) |-> ( ( ( Y o. S ) ` p ) .x. ( G gsum ( n e. N |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = K , .1. , .0. ) , ( i M j ) ) ) ( p ` n ) ) ) ) ) ) ) = .0. )

  proof
    cM
    cB
    wcel
    cK
    cN
    wcel
    cR
    vp
    cP
    cK
    vq
    cv
    cfv
    cK
    wceq
    vq
    cP
    crab
    cdif
    vp
    cv
    #
    cY
    cS
    ccom
    cfv
    cG
    vn
    cN
    vn
    cv
    #
    @1
    @0
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
    cK
    wceq
    c.1
    c.0
    cif
    @2
    @3
    cM
    co
    cif
    cmpt2
    co
    cmpt
    cgsu
    co
    c.x
    co
    cmpt
    cgsu
    co
    c.0
    wceq
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
    cK
    cM
    cN
    cY
    c.0
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
    smadiadetlem1a
    3anidm23
end
