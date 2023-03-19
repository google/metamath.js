include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "ccrg.mm"
include "eqid.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "a1i.mm"
include "w3a.mm"
include "crg.mm"
include "crngring.mm"
include "ringidcl.mm"
include "mp2b.mm"
include "ring0cl.mm"
include "keepel.mm"
include "simp2.mm"
include "simp3.mm"
include "id.mm"
include "syl6eleq.mm"
include "3ad2ant1.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ifcld.mm"
include "matbas2d.mm"

theorem marep01ma
  let cA: class A
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let vk: setvar k
  let cH: class H
  let cI: class I
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  assume marep01ma.a: |- A = ( N Mat R )
  assume marep01ma.b: |- B = ( Base ` A )
  assume marep01ma.r: |- R e. CRing
  assume marep01ma.0: |- .0. = ( 0g ` R )
  assume marep01ma.1: |- .1. = ( 1r ` R )

  disjoint k l
  disjoint B k
  disjoint B l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  assert |- ( M e. B -> ( k e. N , l e. N |-> if ( k = H , if ( l = I , .1. , .0. ) , ( k M l ) ) ) e. B )

  proof
    cM
    cB
    wcel
    #
    vk
    vl
    cA
    cB
    vk
    cv
    #
    cH
    wceq
    #
    vl
    cv
    #
    cI
    wceq
    #
    c.1
    c.0
    cif
    #
    @1
    @3
    cM
    co
    #
    cif
    cR
    cR
    cbs
    cfv
    #
    cN
    ccrg
    marep01ma.a
    @7
    eqid
    #
    marep01ma.b
    @0
    cN
    cfn
    wcel
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
    cR
    ccrg
    wcel
    #
    @0
    marep01ma.r
    a1i
    @0
    @1
    cN
    wcel
    #
    @3
    cN
    wcel
    #
    w3a
    #
    @2
    @5
    @6
    @7
    @5
    @7
    wcel
    @12
    @4
    c.1
    c.0
    @7
    @9
    cR
    crg
    wcel
    #
    c.1
    @7
    wcel
    marep01ma.r
    cR
    crngring
    #
    @7
    cR
    c.1
    @8
    marep01ma.1
    ringidcl
    mp2b
    @9
    @13
    c.0
    @7
    wcel
    marep01ma.r
    @14
    @7
    cR
    c.0
    @8
    marep01ma.0
    ring0cl
    mp2b
    keepel
    a1i
    @12
    @10
    @11
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @6
    @7
    wcel
    @0
    @10
    @11
    simp2
    @0
    @10
    @11
    simp3
    @0
    @10
    @16
    @11
    @0
    cM
    cB
    @15
    @0
    id
    marep01ma.b
    syl6eleq
    3ad2ant1
    cA
    cR
    @1
    @3
    @7
    cM
    cN
    marep01ma.a
    @8
    matecl
    syl3anc
    ifcld
    matbas2d
end
