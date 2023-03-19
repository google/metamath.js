include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmg.mm"
include "co.mm"
include "cpsgn.mm"
include "cz.mm"
include "wceq.mm"
include "c1.mm"
include "cop.mm"
include "c2.mm"
include "cpr.mm"
include "wo.mm"
include "elpri.mm"
include "fveq2.mm"
include "cpmtr.mm"
include "crn.mm"
include "csymg.mm"
include "eqid.mm"
include "psgnprfval1.mm"
include "syl6eq.mm"
include "1z.mm"
include "syl6eqel.mm"
include "cneg.mm"
include "psgnprfval2.mm"
include "neg1z.mm"
include "jaoi.mm"
include "syl.mm"
include "cvv.mm"
include "cn.mm"
include "1ex.mm"
include "2nn.mm"
include "symg2bas.mm"
include "mp2an.mm"
include "eleq2s.mm"
include "zrhmulg.mm"
include "sylan2.mm"
include "a1i.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem m2detleiblem1
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cN: class N
  let cY: class Y
  assume m2detleiblem1.n: |- N = { 1 , 2 }
  assume m2detleiblem1.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume m2detleiblem1.y: |- Y = ( ZRHom ` R )
  assume m2detleiblem1.s: |- S = ( pmSgn ` N )
  assume m2detleiblem1.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ Q e. P ) -> ( Y ` ( S ` Q ) ) = ( ( ( pmSgn ` N ) ` Q ) ( .g ` R ) .1. ) )

  proof
    cR
    crg
    wcel
    #
    cQ
    cP
    wcel
    #
    wa
    #
    cQ
    cS
    cfv
    #
    cY
    cfv
    #
    @3
    c.1
    cR
    cmg
    cfv
    #
    co
    #
    cQ
    cN
    cpsgn
    cfv
    #
    cfv
    #
    c.1
    @5
    co
    @1
    @0
    @3
    cz
    wcel
    #
    @4
    @6
    wceq
    @9
    cQ
    c1
    c1
    cop
    c2
    c2
    cop
    cpr
    #
    c1
    c2
    cop
    c2
    c1
    cop
    cpr
    #
    cpr
    #
    cP
    cQ
    @12
    wcel
    cQ
    @10
    wceq
    #
    cQ
    @11
    wceq
    #
    wo
    @9
    cQ
    @10
    @11
    elpri
    @13
    @9
    @14
    @13
    @3
    c1
    cz
    @13
    @3
    @10
    cS
    cfv
    c1
    cQ
    @10
    cS
    fveq2
    cP
    cN
    cN
    cpmtr
    cfv
    crn
    #
    cN
    csymg
    cfv
    #
    cS
    m2detleiblem1.n
    @16
    eqid
    #
    m2detleiblem1.p
    @15
    eqid
    #
    m2detleiblem1.s
    psgnprfval1
    syl6eq
    1z
    syl6eqel
    @14
    @3
    c1
    cneg
    #
    cz
    @14
    @3
    @11
    cS
    cfv
    @19
    cQ
    @11
    cS
    fveq2
    cP
    cN
    @15
    @16
    cS
    m2detleiblem1.n
    @17
    m2detleiblem1.p
    @18
    m2detleiblem1.s
    psgnprfval2
    syl6eq
    neg1z
    syl6eqel
    jaoi
    syl
    c1
    cvv
    wcel
    c2
    cn
    wcel
    cP
    @12
    wceq
    1ex
    2nn
    cN
    cP
    @16
    c1
    c2
    cvv
    cn
    @17
    m2detleiblem1.p
    m2detleiblem1.n
    symg2bas
    mp2an
    eleq2s
    cR
    @5
    c.1
    cY
    @3
    m2detleiblem1.y
    @5
    eqid
    m2detleiblem1.o
    zrhmulg
    sylan2
    @2
    @3
    @8
    c.1
    @5
    @2
    cQ
    cS
    @7
    cS
    @7
    wceq
    @2
    m2detleiblem1.s
    a1i
    fveq1d
    oveq1d
    eqtrd
end
