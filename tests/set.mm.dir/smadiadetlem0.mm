include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cdif.mm"
include "cif.mm"
include "co.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wa.mm"
include "ccrg.mm"
include "a1i.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "cbs.mm"
include "wral.mm"
include "wi.mm"
include "crg.mm"
include "crngring.mm"
include "mp1i.mm"
include "eldifi.mm"
include "adantl.mm"
include "marep01ma.mm"
include "matepm2cl.mm"
include "syl3anc.mm"
include "weq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "imp.mm"
include "wrex.mm"
include "symgmatr01.mm"
include "3adant1.mm"
include "gsummgp0.mm"
include "ex.mm"

theorem smadiadetlem0
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vq: setvar q
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  assume marep01ma.a: |- A = ( N Mat R )
  assume marep01ma.b: |- B = ( Base ` A )
  assume marep01ma.r: |- R e. CRing
  assume marep01ma.0: |- .0. = ( 0g ` R )
  assume marep01ma.1: |- .1. = ( 1r ` R )
  assume smadiadetlem.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume smadiadetlem.g: |- G = ( mulGrp ` R )

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
  disjoint Q i
  disjoint Q j
  disjoint Q n
  disjoint Q q
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
  disjoint Q m
  disjoint R m
  disjoint .1. m
  disjoint .0. m
  disjoint G m
  assert |- ( ( M e. B /\ K e. N /\ L e. N ) -> ( Q e. ( P \ { q e. P | ( q ` K ) = L } ) -> ( G gsum ( n e. N |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = L , .1. , .0. ) , ( i M j ) ) ) ( Q ` n ) ) ) ) = .0. ) )

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
    cQ
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
    wcel
    #
    cG
    vn
    cN
    vn
    cv
    #
    @6
    cQ
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
    cL
    wceq
    c.1
    c.0
    cif
    @8
    @9
    cM
    co
    cif
    cmpt2
    #
    co
    #
    cmpt
    cgsu
    co
    c.0
    wceq
    @3
    @5
    wa
    #
    @11
    vm
    cv
    #
    @13
    cQ
    cfv
    #
    @10
    co
    #
    cR
    vm
    vn
    cG
    cN
    c.0
    smadiadetlem.g
    marep01ma.0
    cR
    ccrg
    wcel
    #
    @12
    marep01ma.r
    a1i
    @3
    cN
    cfn
    wcel
    #
    @5
    @0
    @1
    @17
    @2
    @0
    @17
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
    @12
    @6
    cN
    wcel
    #
    @11
    cR
    cbs
    cfv
    #
    wcel
    #
    @12
    @15
    @19
    wcel
    #
    vm
    cN
    wral
    #
    @18
    @20
    wi
    @12
    cR
    crg
    wcel
    #
    cQ
    cP
    wcel
    #
    @10
    cB
    wcel
    #
    @22
    @16
    @23
    @12
    marep01ma.r
    cR
    crngring
    mp1i
    @5
    @24
    @3
    cQ
    cP
    @4
    eldifi
    adantl
    @3
    @25
    @5
    @0
    @1
    @25
    @2
    cA
    cB
    cR
    c.1
    vi
    cK
    cL
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
    3ad2ant1
    adantr
    cA
    cB
    cP
    cQ
    cR
    vm
    @10
    cN
    marep01ma.a
    marep01ma.b
    smadiadetlem.p
    matepm2cl
    syl3anc
    @21
    @20
    vm
    @6
    cN
    vm
    vn
    weq
    #
    @15
    @11
    @19
    @26
    @13
    @6
    @14
    @7
    @10
    @26
    id
    @13
    @6
    cQ
    fveq2
    oveq12d
    eleq1d
    rspccv
    syl
    imp
    vn
    vm
    weq
    #
    @11
    @15
    wceq
    @12
    @27
    @6
    @13
    @7
    @14
    @10
    @27
    id
    @6
    @13
    cQ
    fveq2
    oveq12d
    adantl
    @3
    @5
    @15
    c.0
    wceq
    vm
    cN
    wrex
    #
    @1
    @2
    @5
    @28
    wi
    @0
    cP
    cQ
    cR
    c.1
    vi
    vj
    vm
    cK
    cL
    cM
    cN
    c.0
    vq
    smadiadetlem.p
    marep01ma.0
    marep01ma.1
    symgmatr01
    3adant1
    imp
    gsummgp0
    ex
end
