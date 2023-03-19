include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "cur.mm"
include "cif.mm"
include "cbs.mm"
include "simpl2.mm"
include "simp3.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "3adant3.mm"
include "jca.mm"
include "adantr.mm"
include "simpr.mm"
include "matvscacell.mm"
include "syl3anc.mm"
include "simpl1.mm"
include "simprl.mm"
include "simprr.mm"
include "mat1ov.mm"
include "oveq2d.mm"
include "ovif2.mm"
include "ringridm.mm"
include "3adant1.mm"
include "ringrz.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "3eqtrd.mm"

theorem scmatscmide
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let c.as: class .*
  let cJ: class J
  let cN: class N
  let c.0: class .0.
  assume scmatscmide.a: |- A = ( N Mat R )
  assume scmatscmide.b: |- B = ( Base ` R )
  assume scmatscmide.0: |- .0. = ( 0g ` R )
  assume scmatscmide.1: |- .1. = ( 1r ` A )
  assume scmatscmide.m: |- .* = ( .s ` A )


  assert |- ( ( ( N e. Fin /\ R e. Ring /\ C e. B ) /\ ( I e. N /\ J e. N ) ) -> ( I ( C .* .1. ) J ) = if ( I = J , C , .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cC
    cB
    wcel
    #
    w3a
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    wa
    #
    wa
    #
    cI
    cJ
    cC
    c.1
    c.as
    co
    co
    #
    cC
    cI
    cJ
    c.1
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cC
    cI
    cJ
    wceq
    #
    cR
    cur
    cfv
    #
    c.0
    cif
    #
    @10
    co
    #
    @12
    cC
    c.0
    cif
    #
    @7
    @1
    @2
    c.1
    cA
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @6
    @8
    @11
    wceq
    @0
    @1
    @2
    @6
    simpl2
    #
    @3
    @19
    @6
    @3
    @2
    @18
    @0
    @1
    @2
    simp3
    @0
    @1
    @18
    @2
    @0
    @1
    wa
    cA
    crg
    wcel
    @18
    cA
    cR
    cN
    scmatscmide.a
    matring
    @17
    cA
    c.1
    @17
    eqid
    #
    scmatscmide.1
    ringidcl
    syl
    3adant3
    jca
    adantr
    @3
    @6
    simpr
    cA
    @17
    cR
    c.as
    @10
    cI
    cJ
    cB
    cN
    cC
    c.1
    scmatscmide.a
    @21
    scmatscmide.b
    scmatscmide.m
    @10
    eqid
    #
    matvscacell
    syl3anc
    @7
    @9
    @14
    cC
    @10
    @7
    cA
    cR
    c.1
    @13
    cI
    cJ
    cN
    c.0
    scmatscmide.a
    @13
    eqid
    #
    scmatscmide.0
    @0
    @1
    @2
    @6
    simpl1
    @20
    @3
    @4
    @5
    simprl
    @3
    @4
    @5
    simprr
    scmatscmide.1
    mat1ov
    oveq2d
    @3
    @15
    @16
    wceq
    @6
    @3
    @15
    @12
    cC
    @13
    @10
    co
    #
    cC
    c.0
    @10
    co
    #
    cif
    @16
    @12
    cC
    @13
    c.0
    @10
    ovif2
    @3
    @12
    @24
    cC
    @25
    c.0
    @1
    @2
    @24
    cC
    wceq
    @0
    cB
    cR
    @10
    @13
    cC
    scmatscmide.b
    @22
    @23
    ringridm
    3adant1
    @1
    @2
    @25
    c.0
    wceq
    @0
    cB
    cR
    @10
    cC
    c.0
    scmatscmide.b
    @22
    scmatscmide.0
    ringrz
    3adant1
    ifeq12d
    syl5eq
    adantr
    3eqtrd
end
