include "wcel.mm"
include "cv.mm"
include "cltrn.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cdia.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ccnv.mm"
include "co.mm"
include "cmpt.mm"
include "cocaN.mm"
include "docaffvalN.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "cnveqd.mm"
include "rneqd.mm"
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "id.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem docafvalN
  let vx: setvar x
  let vz: setvar z
  let cT: class T
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  assume docaval.j: |- .\/ = ( join ` K )
  assume docaval.m: |- ./\ = ( meet ` K )
  assume docaval.o: |- ._|_ = ( oc ` K )
  assume docaval.h: |- H = ( LHyp ` K )
  assume docaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume docaval.i: |- I = ( ( DIsoA ` K ) ` W )
  assume docaval.n: |- N = ( ( ocA ` K ) ` W )

  disjoint x z
  disjoint K x
  disjoint K z
  disjoint I x
  disjoint I z
  disjoint T x
  disjoint W x
  disjoint W z
  disjoint ./\ k
  disjoint .\/ k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k x
  disjoint k z
  disjoint K k
  disjoint w x
  disjoint w z
  disjoint K w
  disjoint ._|_ k
  disjoint ./\ w
  disjoint .\/ w
  disjoint I w
  disjoint ._|_ w
  disjoint T w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> N = ( x e. ~P T |-> ( I ` ( ( ( ._|_ ` ( `' I ` |^| { z e. ran I | x C_ z } ) ) .\/ ( ._|_ ` W ) ) ./\ W ) ) ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cN
    cW
    vw
    cH
    vx
    vw
    cv
    #
    cK
    cltrn
    cfv
    #
    cfv
    #
    cpw
    #
    vx
    cv
    vz
    cv
    wss
    #
    vz
    @1
    cK
    cdia
    cfv
    #
    cfv
    #
    crn
    #
    crab
    #
    cint
    #
    @7
    ccnv
    #
    cfv
    #
    c.pe
    cfv
    #
    @1
    c.pe
    cfv
    #
    c.or
    co
    #
    @1
    c.an
    co
    #
    @7
    cfv
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vx
    cT
    cpw
    #
    @5
    vz
    cI
    crn
    #
    crab
    #
    cint
    #
    cI
    ccnv
    #
    cfv
    #
    c.pe
    cfv
    #
    cW
    c.pe
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cI
    cfv
    #
    cmpt
    #
    @0
    cN
    cW
    cK
    cocaN
    cfv
    #
    cfv
    @20
    docaval.n
    @0
    cW
    @33
    @19
    vx
    vz
    vw
    cH
    c.or
    cK
    c.an
    c.pe
    cV
    docaval.j
    docaval.m
    docaval.o
    docaval.h
    docaffvalN
    fveq1d
    syl5eq
    vw
    cW
    @18
    @32
    cH
    @19
    @1
    cW
    wceq
    #
    vx
    @4
    @17
    @21
    @31
    @34
    @3
    cT
    @34
    @3
    cW
    @2
    cfv
    #
    cT
    @1
    cW
    @2
    fveq2
    docaval.t
    syl6eqr
    pweqd
    @34
    @16
    @30
    @7
    cI
    @34
    @7
    cW
    @6
    cfv
    cI
    @1
    cW
    @6
    fveq2
    docaval.i
    syl6eqr
    #
    @34
    @15
    @29
    @1
    cW
    c.an
    @34
    @13
    @27
    @14
    @28
    c.or
    @34
    @12
    @26
    c.pe
    @34
    @10
    @24
    @11
    @25
    @34
    @7
    cI
    @36
    cnveqd
    @34
    @9
    @23
    @34
    @8
    @22
    wceq
    @9
    @23
    wceq
    @34
    @7
    cI
    @36
    rneqd
    @5
    vz
    @8
    @22
    rabeq
    syl
    inteqd
    fveq12d
    fveq2d
    @1
    cW
    c.pe
    fveq2
    oveq12d
    @34
    id
    oveq12d
    fveq12d
    mpteq12dv
    @19
    eqid
    vx
    @21
    @31
    cT
    cT
    @35
    cvv
    docaval.t
    cW
    @2
    fvex
    eqeltri
    pwex
    mptex
    fvmpt
    sylan9eq
end
