include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "eqid.mm"
include "mapdval2N.mm"
include "wcel.mm"
include "wa.mm"
include "lcfl1lem.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "r19.42v.mm"
include "simprr.mm"
include "fveq2d.mm"
include "simprl.mm"
include "cbs.mm"
include "chlt.mm"
include "adantr.mm"
include "wss.mm"
include "lssel.mm"
include "sylan.mm"
include "snssd.mm"
include "dochocsp.mm"
include "3eqtr3rd.mm"
include "simpr.mm"
include "eqcomd.mm"
include "weq.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "simpllr.mm"
include "lcfl8a.mm"
include "mpbird.mm"
include "dochocsn.mm"
include "fveq2.mm"
include "sylan9req.mm"
include "jca.mm"
include "impbida.mm"
include "rexbidva.mm"
include "syl5bbr.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "rabbidva2.mm"
include "eqtrd.mm"

theorem mapdval4N
  let wph: wff ph
  let vv: setvar v
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  let vg: setvar g
  let vw: setvar w
  assume mapdval4.h: |- H = ( LHyp ` K )
  assume mapdval4.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval4.s: |- S = ( LSubSp ` U )
  assume mapdval4.f: |- F = ( LFnl ` U )
  assume mapdval4.l: |- L = ( LKer ` U )
  assume mapdval4.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval4.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdval4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdval4.t: |- ( ph -> T e. S )

  disjoint f v
  disjoint F f
  disjoint F v
  disjoint K f
  disjoint L v
  disjoint O v
  disjoint T f
  disjoint T v
  disjoint U v
  disjoint W f
  disjoint f ph
  disjoint ph v
  disjoint f g
  disjoint f w
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint v w
  disjoint F w
  disjoint L g
  disjoint L w
  disjoint O g
  disjoint O w
  disjoint T w
  disjoint U w
  disjoint ph w
  assert |- ( ph -> ( M ` T ) = { f e. F | E. v e. T ( O ` { v } ) = ( L ` f ) } )

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
    vv
    cv
    #
    csn
    #
    cU
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vv
    cT
    wrex
    #
    vf
    vg
    cv
    cL
    cfv
    #
    cO
    cfv
    cO
    cfv
    @9
    wceq
    vg
    cF
    crab
    #
    crab
    @4
    cO
    cfv
    #
    @1
    wceq
    #
    vv
    cT
    wrex
    #
    vf
    cF
    crab
    wph
    vv
    @10
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
    @5
    cO
    cW
    mapdval4.h
    mapdval4.u
    mapdval4.s
    @5
    eqid
    #
    mapdval4.f
    mapdval4.l
    mapdval4.o
    mapdval4.m
    mapdval4.k
    mapdval4.t
    @10
    eqid
    #
    mapdval2N
    wph
    @8
    @13
    vf
    @10
    cF
    @0
    @10
    wcel
    #
    @8
    wa
    #
    @0
    cF
    wcel
    #
    @2
    cO
    cfv
    #
    @1
    wceq
    #
    @8
    wa
    #
    wa
    #
    wph
    @18
    @13
    wa
    @17
    @18
    @20
    wa
    #
    @8
    wa
    @22
    @16
    @23
    @8
    @10
    vg
    cF
    @0
    cL
    cO
    @15
    lcfl1lem
    anbi1i
    @18
    @20
    @8
    anass
    bitri
    wph
    @18
    @21
    @13
    @21
    @20
    @7
    wa
    #
    vv
    cT
    wrex
    wph
    @18
    wa
    #
    @13
    @20
    @7
    vv
    cT
    r19.42v
    @25
    @24
    @12
    vv
    cT
    @25
    @3
    cT
    wcel
    #
    wa
    #
    @24
    @12
    @27
    @24
    wa
    #
    @19
    @6
    cO
    cfv
    @1
    @11
    @28
    @2
    @6
    cO
    @27
    @20
    @7
    simprr
    fveq2d
    @27
    @20
    @7
    simprl
    @28
    cU
    cH
    cK
    @5
    cO
    cU
    cbs
    cfv
    #
    cW
    @4
    mapdval4.h
    mapdval4.u
    mapdval4.o
    @29
    eqid
    #
    @14
    @27
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @24
    @25
    @31
    @26
    wph
    @31
    @18
    mapdval4.k
    adantr
    adantr
    #
    adantr
    @27
    @4
    @29
    wss
    @24
    @27
    @3
    @29
    @25
    cT
    cS
    wcel
    #
    @26
    @3
    @29
    wcel
    #
    wph
    @33
    @18
    mapdval4.t
    adantr
    cS
    cT
    @29
    cU
    @3
    @30
    mapdval4.s
    lssel
    sylan
    #
    snssd
    adantr
    dochocsp
    3eqtr3rd
    @27
    @12
    wa
    #
    @20
    @7
    @36
    @20
    @1
    vw
    cv
    #
    csn
    #
    cO
    cfv
    #
    wceq
    #
    vw
    @29
    wrex
    #
    @36
    @34
    @1
    @11
    wceq
    #
    @41
    @27
    @34
    @12
    @35
    adantr
    @36
    @11
    @1
    @27
    @12
    simpr
    eqcomd
    @40
    @42
    vw
    @3
    @29
    vw
    vv
    weq
    #
    @39
    @11
    @1
    @43
    @38
    @4
    cO
    @37
    @3
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    @36
    vw
    cU
    cF
    @0
    cH
    cK
    cL
    cO
    @29
    cW
    mapdval4.h
    mapdval4.o
    mapdval4.u
    @30
    mapdval4.f
    mapdval4.l
    @27
    @31
    @12
    @32
    adantr
    wph
    @18
    @26
    @12
    simpllr
    lcfl8a
    mpbird
    @36
    @6
    @2
    @27
    @12
    @6
    @11
    cO
    cfv
    @2
    @27
    cU
    cH
    cK
    @5
    cO
    @29
    cW
    @3
    mapdval4.h
    mapdval4.u
    mapdval4.o
    @30
    @14
    @32
    @35
    dochocsn
    @11
    @1
    cO
    fveq2
    sylan9req
    eqcomd
    jca
    impbida
    rexbidva
    syl5bbr
    pm5.32da
    syl5bb
    rabbidva2
    eqtrd
end
