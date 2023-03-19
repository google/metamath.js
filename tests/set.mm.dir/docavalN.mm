include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ccnv.mm"
include "co.mm"
include "cmpt.mm"
include "wceq.mm"
include "docafvalN.mm"
include "adantr.mm"
include "fveq1d.mm"
include "cvv.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "adantl.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem docavalN
  let vz: setvar z
  let cT: class T
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  assume docaval.j: |- .\/ = ( join ` K )
  assume docaval.m: |- ./\ = ( meet ` K )
  assume docaval.o: |- ._|_ = ( oc ` K )
  assume docaval.h: |- H = ( LHyp ` K )
  assume docaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume docaval.i: |- I = ( ( DIsoA ` K ) ` W )
  assume docaval.n: |- N = ( ( ocA ` K ) ` W )

  disjoint K z
  disjoint I z
  disjoint W z
  disjoint T z
  disjoint X z
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
  disjoint x z
  disjoint K x
  disjoint ._|_ k
  disjoint ./\ w
  disjoint .\/ w
  disjoint I w
  disjoint I x
  disjoint ._|_ w
  disjoint T w
  disjoint T x
  disjoint W w
  disjoint W x
  disjoint ./\ x
  disjoint .\/ x
  disjoint ._|_ x
  disjoint X x
  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ T ) -> ( N ` X ) = ( I ` ( ( ( ._|_ ` ( `' I ` |^| { z e. ran I | X C_ z } ) ) .\/ ( ._|_ ` W ) ) ./\ W ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cT
    wss
    #
    wa
    #
    cX
    cN
    cfv
    cX
    vx
    cT
    cpw
    #
    vx
    cv
    #
    vz
    cv
    #
    wss
    #
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
    cfv
    #
    cX
    @5
    wss
    #
    vz
    @7
    crab
    #
    cint
    #
    @10
    cfv
    #
    c.pe
    cfv
    #
    @13
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
    @2
    cX
    cN
    @17
    @0
    cN
    @17
    wceq
    @1
    vx
    vz
    cT
    cH
    cI
    c.or
    cK
    c.an
    cN
    c.pe
    chlt
    cW
    docaval.j
    docaval.m
    docaval.o
    docaval.h
    docaval.t
    docaval.i
    docaval.n
    docafvalN
    adantr
    fveq1d
    @2
    cX
    @3
    wcel
    #
    @26
    cvv
    wcel
    @18
    @26
    wceq
    @1
    @27
    @0
    @27
    @1
    cX
    cT
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    docaval.t
    cW
    @28
    fvex
    eqeltri
    elpw2
    biimpri
    adantl
    @25
    cI
    fvex
    vx
    cX
    @16
    @26
    @3
    cvv
    @17
    @4
    cX
    wceq
    #
    @15
    @25
    cI
    @29
    @14
    @24
    cW
    c.an
    @29
    @12
    @23
    @13
    c.or
    @29
    @11
    @22
    c.pe
    @29
    @9
    @21
    @10
    @29
    @8
    @20
    @29
    @6
    @19
    vz
    @7
    @4
    cX
    @5
    sseq1
    rabbidv
    inteqd
    fveq2d
    fveq2d
    oveq1d
    oveq1d
    fveq2d
    @17
    eqid
    fvmptg
    sylancl
    eqtrd
end
