include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "crab.mm"
include "clss.mm"
include "chlt.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdval.mm"
include "ad2antrr.mm"
include "snssd.mm"
include "lspssv.mm"
include "simprr.mm"
include "dochss.mm"
include "syl3anc.mm"
include "dochocsp.mm"
include "simprl.mm"
include "3sstr3d.mm"
include "simplr.mm"
include "simpr.mm"
include "lcfl9a.mm"
include "lkrssv.mm"
include "dochocsn.mm"
include "sseqtrd.mm"
include "jca.mm"
include "impbida.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem mapdsn
  let wph: wff ph
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  assume mapdsn.h: |- H = ( LHyp ` K )
  assume mapdsn.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdsn.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdsn.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdsn.v: |- V = ( Base ` U )
  assume mapdsn.n: |- N = ( LSpan ` U )
  assume mapdsn.f: |- F = ( LFnl ` U )
  assume mapdsn.l: |- L = ( LKer ` U )
  assume mapdsn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdsn.x: |- ( ph -> X e. V )

  disjoint F f
  disjoint K f
  disjoint N f
  disjoint W f
  disjoint X f
  disjoint f ph
  assert |- ( ph -> ( M ` ( N ` { X } ) ) = { f e. F | ( O ` { X } ) C_ ( L ` f ) } )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
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
    cO
    cfv
    #
    @3
    wceq
    #
    @4
    @1
    wss
    #
    wa
    #
    vf
    cF
    crab
    @0
    cO
    cfv
    #
    @3
    wss
    #
    vf
    cF
    crab
    wph
    cU
    clss
    cfv
    #
    @1
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    mapdsn.h
    mapdsn.u
    @11
    eqid
    #
    mapdsn.f
    mapdsn.l
    mapdsn.o
    mapdsn.m
    mapdsn.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @1
    @11
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdsn.h
    mapdsn.u
    mapdsn.k
    dvhlmod
    #
    mapdsn.x
    @11
    cN
    cV
    cU
    cX
    mapdsn.v
    @12
    mapdsn.n
    lspsncl
    syl2anc
    mapdval
    wph
    @8
    @10
    vf
    cF
    wph
    @2
    cF
    wcel
    #
    wa
    #
    @8
    @10
    @17
    @8
    wa
    #
    @1
    cO
    cfv
    #
    @5
    @9
    @3
    @18
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cV
    wss
    #
    @7
    @19
    @5
    wss
    wph
    @20
    @16
    @8
    mapdsn.k
    ad2antrr
    wph
    @21
    @16
    @8
    wph
    @13
    @0
    cV
    wss
    @21
    @15
    wph
    cX
    cV
    mapdsn.x
    snssd
    #
    @0
    cN
    cV
    cU
    mapdsn.v
    mapdsn.n
    lspssv
    syl2anc
    ad2antrr
    @17
    @6
    @7
    simprr
    cU
    cH
    cK
    cO
    cV
    cW
    @4
    @1
    mapdsn.h
    mapdsn.u
    mapdsn.v
    mapdsn.o
    dochss
    syl3anc
    wph
    @19
    @9
    wceq
    @16
    @8
    wph
    cU
    cH
    cK
    cN
    cO
    cV
    cW
    @0
    mapdsn.h
    mapdsn.u
    mapdsn.o
    mapdsn.v
    mapdsn.n
    mapdsn.k
    @22
    dochocsp
    ad2antrr
    @17
    @6
    @7
    simprl
    3sstr3d
    @17
    @10
    wa
    #
    @6
    @7
    @23
    cU
    cF
    @2
    cH
    cK
    cL
    cO
    cV
    cW
    cX
    mapdsn.h
    mapdsn.o
    mapdsn.u
    mapdsn.v
    mapdsn.f
    mapdsn.l
    wph
    @20
    @16
    @10
    mapdsn.k
    ad2antrr
    #
    wph
    @16
    @10
    simplr
    #
    wph
    @14
    @16
    @10
    mapdsn.x
    ad2antrr
    @17
    @10
    simpr
    #
    lcfl9a
    @23
    @4
    @9
    cO
    cfv
    #
    @1
    @23
    @20
    @3
    cV
    wss
    @10
    @4
    @27
    wss
    @24
    @23
    cF
    @2
    cL
    cV
    cU
    mapdsn.v
    mapdsn.f
    mapdsn.l
    wph
    @13
    @16
    @10
    @15
    ad2antrr
    @25
    lkrssv
    @26
    cU
    cH
    cK
    cO
    cV
    cW
    @9
    @3
    mapdsn.h
    mapdsn.u
    mapdsn.v
    mapdsn.o
    dochss
    syl3anc
    wph
    @27
    @1
    wceq
    @16
    @10
    wph
    cU
    cH
    cK
    cN
    cO
    cV
    cW
    cX
    mapdsn.h
    mapdsn.u
    mapdsn.o
    mapdsn.v
    mapdsn.n
    mapdsn.k
    mapdsn.x
    dochocsn
    ad2antrr
    sseqtrd
    jca
    impbida
    rabbidva
    eqtrd
end
