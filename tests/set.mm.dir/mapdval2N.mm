include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "chlt.mm"
include "mapdvalc.mm"
include "wcel.mm"
include "wa.mm"
include "clsa.mm"
include "wi.mm"
include "c0g.mm"
include "cbs.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "eqid.mm"
include "islsati.mm"
include "syl2anc.mm"
include "simprr.mm"
include "eqsstr3d.mm"
include "adantr.mm"
include "simprl.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "lss0cl.mm"
include "simpr.mm"
include "lspsn0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "adantlr.mm"
include "a1d.mm"
include "lcfl1lem.mm"
include "simplbi.mm"
include "adantl.mm"
include "dochsat0.mm"
include "mpjaodan.mm"
include "w3a.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "lspsnel5a.mm"
include "eqsstrd.mm"
include "rexlimdv3a.mm"
include "impbid.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem mapdval2N
  let wph: wff ph
  let vv: setvar v
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  assume mapdval2.h: |- H = ( LHyp ` K )
  assume mapdval2.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval2.s: |- S = ( LSubSp ` U )
  assume mapdval2.n: |- N = ( LSpan ` U )
  assume mapdval2.f: |- F = ( LFnl ` U )
  assume mapdval2.l: |- L = ( LKer ` U )
  assume mapdval2.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval2.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdval2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdval2.t: |- ( ph -> T e. S )
  assume mapdval2.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }

  disjoint C v
  disjoint f g
  disjoint F f
  disjoint F g
  disjoint K f
  disjoint g v
  disjoint L g
  disjoint L v
  disjoint N v
  disjoint O g
  disjoint O v
  disjoint f v
  disjoint T f
  disjoint T v
  disjoint U v
  disjoint W f
  disjoint f ph
  disjoint ph v
  assert |- ( ph -> ( M ` T ) = { f e. C | E. v e. T ( O ` ( L ` f ) ) = ( N ` { v } ) } )

  proof
    wph
    cT
    cM
    cfv
    vf
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cT
    wss
    #
    vf
    cC
    crab
    @2
    vv
    cv
    #
    csn
    #
    cN
    cfv
    #
    wceq
    #
    vv
    cT
    wrex
    #
    vf
    cC
    crab
    wph
    cC
    cS
    cT
    cU
    vf
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    mapdval2.h
    mapdval2.u
    mapdval2.s
    mapdval2.f
    mapdval2.l
    mapdval2.o
    mapdval2.m
    mapdval2.k
    mapdval2.t
    mapdval2.c
    mapdvalc
    wph
    @3
    @8
    vf
    cC
    wph
    @0
    cC
    wcel
    #
    wa
    #
    @3
    @8
    @10
    @2
    cU
    clsa
    cfv
    #
    wcel
    #
    @3
    @8
    wi
    @2
    cU
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @10
    @12
    wa
    #
    @3
    @8
    @16
    @3
    wa
    #
    @7
    vv
    cU
    cbs
    cfv
    #
    wrex
    #
    @8
    @17
    cU
    clmod
    wcel
    #
    @12
    @19
    wph
    @20
    @9
    @12
    @3
    wph
    cU
    cH
    cK
    cW
    mapdval2.h
    mapdval2.u
    mapdval2.k
    dvhlmod
    #
    ad3antrrr
    @10
    @12
    @3
    simplr
    vv
    @11
    @2
    cN
    @18
    cU
    clmod
    @18
    eqid
    #
    mapdval2.n
    @11
    eqid
    #
    islsati
    syl2anc
    @17
    @7
    @7
    vv
    @18
    cT
    @17
    @4
    @18
    wcel
    #
    @7
    wa
    #
    @4
    cT
    wcel
    #
    @7
    wa
    @17
    @25
    wa
    #
    @26
    @7
    @27
    @26
    @6
    cT
    wss
    @27
    @6
    @2
    cT
    @17
    @24
    @7
    simprr
    #
    @16
    @3
    @25
    simplr
    eqsstr3d
    @27
    cS
    cT
    cN
    @18
    cU
    @4
    @22
    mapdval2.s
    mapdval2.n
    @10
    @20
    @12
    @3
    @25
    wph
    @20
    @9
    @21
    adantr
    #
    ad3antrrr
    @10
    cT
    cS
    wcel
    #
    @12
    @3
    @25
    wph
    @30
    @9
    mapdval2.t
    adantr
    #
    ad3antrrr
    @17
    @24
    @7
    simprl
    lspsnel5
    mpbird
    @28
    jca
    ex
    reximdv2
    mpd
    ex
    @10
    @15
    wa
    @8
    @3
    wph
    @15
    @8
    @9
    wph
    @15
    wa
    #
    @13
    cT
    wcel
    #
    @2
    @14
    cN
    cfv
    #
    wceq
    #
    @8
    wph
    @33
    @15
    wph
    @20
    @30
    @33
    @21
    mapdval2.t
    cS
    cT
    cU
    @13
    @13
    eqid
    #
    mapdval2.s
    lss0cl
    syl2anc
    adantr
    @32
    @2
    @14
    @34
    wph
    @15
    simpr
    @32
    @20
    @34
    @14
    wceq
    wph
    @20
    @15
    @21
    adantr
    cN
    cU
    @13
    @36
    mapdval2.n
    lspsn0
    syl
    eqtr4d
    @7
    @35
    vv
    @13
    cT
    @4
    @13
    wceq
    #
    @6
    @34
    @2
    @37
    @5
    @14
    cN
    @4
    @13
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    adantlr
    a1d
    @10
    @11
    cU
    cF
    @0
    cH
    cK
    cL
    cO
    cW
    @13
    mapdval2.h
    mapdval2.o
    mapdval2.u
    @36
    @23
    mapdval2.f
    mapdval2.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @9
    mapdval2.k
    adantr
    @9
    @0
    cF
    wcel
    #
    wph
    @9
    @38
    @2
    cO
    cfv
    @1
    wceq
    cC
    vg
    cF
    @0
    cL
    cO
    mapdval2.c
    lcfl1lem
    simplbi
    adantl
    dochsat0
    mpjaodan
    @10
    @7
    @3
    vv
    cT
    @10
    @26
    @7
    w3a
    #
    @2
    @6
    cT
    @10
    @26
    @7
    simp3
    @39
    cS
    cT
    cN
    cU
    @4
    mapdval2.s
    mapdval2.n
    @10
    @26
    @20
    @7
    @29
    3ad2ant1
    @10
    @26
    @30
    @7
    @31
    3ad2ant1
    @10
    @26
    @7
    simp2
    lspsnel5a
    eqsstrd
    rexlimdv3a
    impbid
    rabbidva
    eqtrd
end
