include "crg.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cop.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "cpsgn.mm"
include "cmg.mm"
include "co.mm"
include "cneg.mm"
include "cvv.mm"
include "cn.mm"
include "1ex.mm"
include "2nn.mm"
include "prex.mm"
include "prid2.mm"
include "csymg.mm"
include "eqid.mm"
include "symg2bas.mm"
include "syl5eleqr.mm"
include "mp2an.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "m2detleiblem1.mm"
include "sylan2.mm"
include "fveq2.mm"
include "adantl.mm"
include "cpmtr.mm"
include "crn.mm"
include "psgnprfval2.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "cbs.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "mulgm1.mm"
include "syl2anc.mm"
include "adantr.mm"
include "3eqtrd.mm"

theorem m2detleiblem6
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cI: class I
  let cN: class N
  let cY: class Y
  assume m2detleiblem1.n: |- N = { 1 , 2 }
  assume m2detleiblem1.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume m2detleiblem1.y: |- Y = ( ZRHom ` R )
  assume m2detleiblem1.s: |- S = ( pmSgn ` N )
  assume m2detleiblem1.o: |- .1. = ( 1r ` R )
  assume m2detleiblem1.i: |- I = ( invg ` R )


  assert |- ( ( R e. Ring /\ Q = { <. 1 , 2 >. , <. 2 , 1 >. } ) -> ( Y ` ( S ` Q ) ) = ( I ` .1. ) )

  proof
    cR
    crg
    wcel
    #
    cQ
    c1
    c2
    cop
    #
    c2
    c1
    cop
    #
    cpr
    #
    wceq
    #
    wa
    #
    cQ
    cS
    cfv
    cY
    cfv
    #
    cQ
    cN
    cpsgn
    cfv
    #
    cfv
    #
    c.1
    cR
    cmg
    cfv
    #
    co
    #
    c1
    cneg
    #
    c.1
    @9
    co
    #
    c.1
    cI
    cfv
    #
    @4
    @0
    cQ
    cP
    wcel
    #
    @6
    @10
    wceq
    @4
    @14
    @3
    cP
    wcel
    #
    c1
    cvv
    wcel
    #
    c2
    cn
    wcel
    #
    @15
    1ex
    2nn
    @16
    @17
    wa
    @3
    c1
    c1
    cop
    c2
    c2
    cop
    cpr
    #
    @3
    cpr
    cP
    @18
    @3
    @1
    @2
    prex
    prid2
    cN
    cP
    cN
    csymg
    cfv
    #
    c1
    c2
    cvv
    cn
    @19
    eqid
    #
    m2detleiblem1.p
    m2detleiblem1.n
    symg2bas
    syl5eleqr
    mp2an
    cQ
    @3
    cP
    eleq1
    mpbiri
    cP
    cQ
    cR
    cS
    c.1
    cN
    cY
    m2detleiblem1.n
    m2detleiblem1.p
    m2detleiblem1.y
    m2detleiblem1.s
    m2detleiblem1.o
    m2detleiblem1
    sylan2
    @5
    @8
    @11
    c.1
    @9
    @5
    @8
    @3
    @7
    cfv
    #
    @11
    @4
    @8
    @21
    wceq
    @0
    cQ
    @3
    @7
    fveq2
    adantl
    cP
    cN
    cN
    cpmtr
    cfv
    crn
    #
    @19
    @7
    m2detleiblem1.n
    @20
    m2detleiblem1.p
    @22
    eqid
    @7
    eqid
    psgnprfval2
    syl6eq
    oveq1d
    @0
    @12
    @13
    wceq
    #
    @4
    @0
    cR
    cgrp
    wcel
    c.1
    cR
    cbs
    cfv
    #
    wcel
    @23
    cR
    ringgrp
    @24
    cR
    c.1
    @24
    eqid
    #
    m2detleiblem1.o
    ringidcl
    @24
    @9
    cR
    cI
    c.1
    @25
    @9
    eqid
    m2detleiblem1.i
    mulgm1
    syl2anc
    adantr
    3eqtrd
end
