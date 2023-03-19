include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccrg.mm"
include "wceq.mm"
include "cif.mm"
include "co.mm"
include "cmpt2.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "cbs.mm"
include "a1i.mm"
include "marep01ma.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "madetsmelbas2.mm"
include "syl3anc.mm"

theorem smadiadetlem1
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
  assert |- ( ( ( M e. B /\ K e. N ) /\ p e. P ) -> ( ( ( Y o. S ) ` p ) ( .r ` R ) ( G gsum ( n e. N |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = K , .1. , .0. ) , ( i M j ) ) ) ( p ` n ) ) ) ) ) e. ( Base ` R ) )

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
    vp
    cv
    #
    cP
    wcel
    #
    wa
    #
    cR
    ccrg
    wcel
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
    @7
    @8
    cM
    co
    cif
    cmpt2
    #
    cB
    wcel
    #
    @4
    @3
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
    @11
    @3
    cfv
    @9
    co
    cmpt
    cgsu
    co
    cR
    cmulr
    cfv
    co
    cR
    cbs
    cfv
    wcel
    @6
    @5
    marep01ma.r
    a1i
    @0
    @10
    @1
    @4
    cA
    cB
    cR
    c.1
    vi
    cK
    cK
    cM
    cN
    c.0
    vj
    marep01ma.a
    marep01ma.b
    marep01ma.r
    marep01ma.0
    marep01ma.1
    marep01ma
    ad2antrr
    @2
    @4
    simpr
    cA
    cB
    cP
    @3
    cR
    cS
    vn
    cG
    @9
    cN
    cY
    smadiadetlem.p
    madetminlem.s
    madetminlem.y
    marep01ma.a
    marep01ma.b
    smadiadetlem.g
    madetsmelbas2
    syl3anc
end
