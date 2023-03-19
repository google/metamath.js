include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cif.mm"
include "wrex.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "eqid.mm"
include "scmatscmid.mm"
include "wi.mm"
include "oveq.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpr.mm"
include "simplr.mm"
include "scmatscmide.mm"
include "syl31anc.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "reximdva.mm"
include "mpid.mm"
include "imp.mm"

theorem scmate
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vc: setvar c
  let vm: setvar m
  assume scmatmat.a: |- A = ( N Mat R )
  assume scmatmat.b: |- B = ( Base ` A )
  assume scmatmat.s: |- S = ( N ScMat R )
  assume scmate.k: |- K = ( Base ` R )
  assume scmate.0: |- .0. = ( 0g ` R )

  disjoint M c
  disjoint N c
  disjoint R c
  disjoint I c
  disjoint J c
  disjoint K c
  disjoint S c
  disjoint M m
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. S ) /\ ( I e. N /\ J e. N ) ) -> E. c e. K ( I M J ) = if ( I = J , c , .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cS
    wcel
    #
    w3a
    #
    cI
    cN
    wcel
    cJ
    cN
    wcel
    wa
    #
    cI
    cJ
    cM
    co
    #
    cI
    cJ
    wceq
    vc
    cv
    #
    c.0
    cif
    #
    wceq
    #
    vc
    cK
    wrex
    #
    @3
    @4
    cM
    @6
    cA
    cur
    cfv
    #
    cA
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cK
    wrex
    #
    @9
    cA
    cB
    cR
    cS
    @11
    @10
    cK
    cM
    cN
    crg
    vc
    scmate.k
    scmatmat.a
    scmatmat.b
    @10
    eqid
    #
    @11
    eqid
    #
    scmatmat.s
    scmatscmid
    @3
    @4
    @14
    @9
    wi
    @3
    @4
    wa
    #
    @13
    @8
    vc
    cK
    @17
    @6
    cK
    wcel
    #
    wa
    #
    @13
    @8
    @13
    @19
    @5
    cI
    cJ
    @12
    co
    #
    @7
    cI
    cJ
    cM
    @12
    oveq
    @19
    @0
    @1
    @18
    @4
    @20
    @7
    wceq
    @0
    @1
    @2
    @4
    @18
    simpll1
    @0
    @1
    @2
    @4
    @18
    simpll2
    @17
    @18
    simpr
    @3
    @4
    @18
    simplr
    cA
    cK
    @6
    cR
    @10
    cI
    @11
    cJ
    cN
    c.0
    scmatmat.a
    scmate.k
    scmate.0
    @15
    @16
    scmatscmide
    syl31anc
    sylan9eqr
    ex
    reximdva
    ex
    mpid
    imp
end
