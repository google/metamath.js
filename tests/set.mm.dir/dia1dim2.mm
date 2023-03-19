include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "cab.mm"
include "ctendo.mm"
include "csn.mm"
include "eqid.mm"
include "dvabase.mm"
include "adantr.mm"
include "rexeqdv.mm"
include "dvavsca.mm"
include "anass1rs.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "abbidv.mm"
include "clmod.mm"
include "clvec.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "simpr.mm"
include "dvavbase.mm"
include "eleqtrrd.mm"
include "lspsn.mm"
include "syl2anc.mm"
include "dia1dim.mm"
include "3eqtr4rd.mm"

theorem dia1dim2
  let cR: class R
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cW: class W
  let vg: setvar g
  let vs: setvar s
  assume dia1dim2.h: |- H = ( LHyp ` K )
  assume dia1dim2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia1dim2.r: |- R = ( ( trL ` K ) ` W )
  assume dva1dim2.u: |- U = ( ( DVecA ` K ) ` W )
  assume dia1dim2.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dva1dim2.n: |- N = ( LSpan ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( I ` ( R ` F ) ) = ( N ` { F } ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    wa
    #
    vg
    cv
    #
    vs
    cv
    #
    cF
    cU
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vs
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    vg
    cab
    #
    @3
    cF
    @4
    cfv
    #
    wceq
    #
    vs
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wrex
    #
    vg
    cab
    cF
    csn
    cN
    cfv
    #
    cF
    cR
    cfv
    cI
    cfv
    @2
    @10
    @15
    vg
    @2
    @10
    @7
    vs
    @14
    wrex
    @15
    @2
    @7
    vs
    @9
    @14
    @0
    @9
    @14
    wceq
    @1
    @9
    cU
    @14
    @8
    cH
    cK
    cW
    chlt
    dia1dim2.h
    @14
    eqid
    #
    dva1dim2.u
    @8
    eqid
    #
    @9
    eqid
    #
    dvabase
    adantr
    rexeqdv
    @2
    @7
    @13
    vs
    @14
    @2
    @4
    @14
    wcel
    #
    wa
    @6
    @12
    @3
    @0
    @20
    @1
    @6
    @12
    wceq
    @4
    cT
    @5
    cU
    @14
    cF
    cH
    cK
    chlt
    cW
    dia1dim2.h
    dia1dim2.t
    @17
    dva1dim2.u
    @5
    eqid
    #
    dvavsca
    anass1rs
    eqeq2d
    rexbidva
    bitrd
    abbidv
    @2
    cU
    clmod
    wcel
    #
    cF
    cU
    cbs
    cfv
    #
    wcel
    @16
    @11
    wceq
    @2
    cU
    clvec
    wcel
    #
    @22
    @0
    @24
    @1
    cU
    cH
    cK
    cW
    dia1dim2.h
    dva1dim2.u
    dvalvec
    adantr
    cU
    lveclmod
    syl
    @2
    cF
    cT
    @23
    @0
    @1
    simpr
    @0
    @23
    cT
    wceq
    @1
    cT
    cU
    cH
    cK
    @23
    cW
    chlt
    dia1dim2.h
    dia1dim2.t
    dva1dim2.u
    @23
    eqid
    #
    dvavbase
    adantr
    eleqtrrd
    vg
    @5
    vs
    @8
    @9
    cN
    @23
    cU
    cF
    @18
    @19
    @25
    @21
    dva1dim2.n
    lspsn
    syl2anc
    cR
    cT
    vg
    @14
    cF
    cH
    cI
    cK
    cW
    vs
    dia1dim2.h
    dia1dim2.t
    dia1dim2.r
    @17
    dia1dim2.i
    dia1dim
    3eqtr4rd
end
