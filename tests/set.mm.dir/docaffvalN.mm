include "wcel.mm"
include "cvv.mm"
include "cocaN.mm"
include "cfv.mm"
include "cv.mm"
include "cltrn.mm"
include "cpw.mm"
include "wss.mm"
include "cdia.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ccnv.mm"
include "co.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "coc.mm"
include "cjn.mm"
include "cmee.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "pweqd.mm"
include "cnveqd.mm"
include "rneqd.mm"
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "fveq12d.mm"
include "oveq123d.mm"
include "eqidd.mm"
include "mpteq12dv.mm"
include "df-docaN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem docaffvalN
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cV: class V
  let vk: setvar k
  assume docaval.j: |- .\/ = ( join ` K )
  assume docaval.m: |- ./\ = ( meet ` K )
  assume docaval.o: |- ._|_ = ( oc ` K )
  assume docaval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint w x
  disjoint w z
  disjoint K w
  disjoint x z
  disjoint K x
  disjoint K z
  disjoint ./\ k
  disjoint .\/ k
  disjoint k w
  disjoint H k
  disjoint k x
  disjoint k z
  disjoint K k
  disjoint ._|_ k
  assert |- ( K e. V -> ( ocA ` K ) = ( w e. H |-> ( x e. ~P ( ( LTrn ` K ) ` w ) |-> ( ( ( DIsoA ` K ) ` w ) ` ( ( ( ._|_ ` ( `' ( ( DIsoA ` K ) ` w ) ` |^| { z e. ran ( ( DIsoA ` K ) ` w ) | x C_ z } ) ) .\/ ( ._|_ ` w ) ) ./\ w ) ) ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cocaN
    cfv
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
    @0
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
    @6
    ccnv
    #
    cfv
    #
    c.pe
    cfv
    #
    @0
    c.pe
    cfv
    #
    c.or
    co
    #
    @0
    c.an
    co
    #
    @6
    cfv
    #
    cmpt
    #
    cmpt
    #
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vx
    @0
    @19
    cltrn
    cfv
    #
    cfv
    #
    cpw
    #
    @4
    vz
    @0
    @19
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
    @25
    ccnv
    #
    cfv
    #
    @19
    coc
    cfv
    #
    cfv
    #
    @0
    @31
    cfv
    #
    @19
    cjn
    cfv
    #
    co
    #
    @0
    @19
    cmee
    cfv
    #
    co
    #
    @25
    cfv
    #
    cmpt
    #
    cmpt
    @18
    cvv
    cocaN
    @19
    cK
    wceq
    #
    vw
    @20
    @39
    cH
    @17
    @40
    @20
    cK
    clh
    cfv
    #
    cH
    @19
    cK
    clh
    fveq2
    docaval.h
    syl6eqr
    @40
    vx
    @23
    @38
    @3
    @16
    @40
    @22
    @2
    @40
    @0
    @21
    @1
    @19
    cK
    cltrn
    fveq2
    fveq1d
    pweqd
    @40
    @37
    @15
    @25
    @6
    @40
    @0
    @24
    @5
    @19
    cK
    cdia
    fveq2
    fveq1d
    #
    @40
    @35
    @14
    @0
    @0
    @36
    c.an
    @40
    @36
    cK
    cmee
    cfv
    c.an
    @19
    cK
    cmee
    fveq2
    docaval.m
    syl6eqr
    @40
    @32
    @12
    @33
    @13
    @34
    c.or
    @40
    @34
    cK
    cjn
    cfv
    c.or
    @19
    cK
    cjn
    fveq2
    docaval.j
    syl6eqr
    @40
    @30
    @11
    @31
    c.pe
    @40
    @31
    cK
    coc
    cfv
    c.pe
    @19
    cK
    coc
    fveq2
    docaval.o
    syl6eqr
    #
    @40
    @28
    @9
    @29
    @10
    @40
    @25
    @6
    @42
    cnveqd
    @40
    @27
    @8
    @40
    @26
    @7
    wceq
    @27
    @8
    wceq
    @40
    @25
    @6
    @42
    rneqd
    @4
    vz
    @26
    @7
    rabeq
    syl
    inteqd
    fveq12d
    fveq12d
    @40
    @0
    @31
    c.pe
    @43
    fveq1d
    oveq123d
    @40
    @0
    eqidd
    oveq123d
    fveq12d
    mpteq12dv
    mpteq12dv
    vx
    vz
    vw
    vk
    df-docaN
    vw
    cH
    @17
    cH
    @41
    cvv
    docaval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
