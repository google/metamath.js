include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "wa.mm"
include "dochoc1.mm"
include "adantr.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lkrssv.mm"
include "csn.mm"
include "sneq.mm"
include "fveq2d.mm"
include "chlt.mm"
include "wcel.mm"
include "eqid.mm"
include "doch0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "wne.mm"
include "cdih.mm"
include "crn.mm"
include "snssd.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "clsh.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "cdif.mm"
include "simprl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dochsnshp.mm"
include "simprr.mm"
include "wb.mm"
include "lkrshp4.mm"
include "mpbid.mm"
include "lshpcmp.mm"
include "3eqtr3d.mm"
include "pm2.61da2ne.mm"

theorem lcfl9a
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcfl9a.h: |- H = ( LHyp ` K )
  assume lcfl9a.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl9a.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl9a.v: |- V = ( Base ` U )
  assume lcfl9a.f: |- F = ( LFnl ` U )
  assume lcfl9a.l: |- L = ( LKer ` U )
  assume lcfl9a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl9a.g: |- ( ph -> G e. F )
  assume lcfl9a.x: |- ( ph -> X e. V )
  assume lcfl9a.s: |- ( ph -> ( ._|_ ` { X } ) C_ ( L ` G ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) )

  proof
    wph
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @0
    wceq
    cX
    cU
    c0g
    cfv
    #
    @0
    cV
    wph
    cX
    @3
    wceq
    #
    wa
    #
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    @2
    @0
    wph
    @7
    cV
    wceq
    #
    @4
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    lcfl9a.h
    lcfl9a.u
    lcfl9a.o
    lcfl9a.v
    lcfl9a.k
    dochoc1
    #
    adantr
    @5
    @1
    @6
    c.pe
    @5
    @0
    cV
    c.pe
    @5
    @0
    cV
    wph
    @0
    cV
    wss
    @4
    wph
    cF
    cG
    cL
    cV
    cU
    lcfl9a.v
    lcfl9a.f
    lcfl9a.l
    wph
    cU
    cH
    cK
    cW
    lcfl9a.h
    lcfl9a.u
    lcfl9a.k
    dvhlmod
    lcfl9a.g
    lkrssv
    adantr
    @5
    cV
    cX
    csn
    #
    c.pe
    cfv
    #
    @0
    @4
    wph
    @11
    @3
    csn
    #
    c.pe
    cfv
    #
    cV
    @4
    @10
    @12
    c.pe
    cX
    @3
    sneq
    fveq2d
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @13
    cV
    wceq
    lcfl9a.k
    cU
    cH
    cK
    c.pe
    cV
    cW
    @3
    lcfl9a.h
    lcfl9a.u
    lcfl9a.o
    lcfl9a.v
    @3
    eqid
    #
    doch0
    syl
    sylan9eqr
    wph
    @11
    @0
    wss
    #
    @4
    lcfl9a.s
    adantr
    eqsstr3d
    eqssd
    #
    fveq2d
    fveq2d
    @17
    3eqtr4d
    wph
    @0
    cV
    wceq
    #
    wa
    #
    @7
    cV
    @2
    @0
    wph
    @8
    @18
    @9
    adantr
    @19
    @1
    @6
    c.pe
    @19
    @0
    cV
    c.pe
    wph
    @18
    simpr
    #
    fveq2d
    fveq2d
    @20
    3eqtr4d
    wph
    cX
    @3
    wne
    #
    @0
    cV
    wne
    #
    wa
    #
    wa
    #
    @11
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @11
    @2
    @0
    wph
    @26
    @11
    wceq
    #
    @23
    wph
    @14
    @11
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @27
    lcfl9a.k
    wph
    @14
    @10
    cV
    wss
    @29
    lcfl9a.k
    wph
    cX
    cV
    lcfl9a.x
    snssd
    cU
    cH
    @28
    cK
    c.pe
    cV
    cW
    @10
    lcfl9a.h
    @28
    eqid
    #
    lcfl9a.u
    lcfl9a.v
    lcfl9a.o
    dochcl
    syl2anc
    cH
    @28
    cK
    c.pe
    cW
    @11
    lcfl9a.h
    @30
    lcfl9a.o
    dochoc
    syl2anc
    adantr
    @24
    @25
    @1
    c.pe
    @24
    @11
    @0
    c.pe
    @24
    @16
    @11
    @0
    wceq
    wph
    @16
    @23
    lcfl9a.s
    adantr
    @24
    @11
    @0
    cU
    clsh
    cfv
    #
    cU
    @31
    eqid
    #
    wph
    cU
    clvec
    wcel
    @23
    wph
    cU
    cH
    cK
    cW
    lcfl9a.h
    lcfl9a.u
    lcfl9a.k
    dvhlvec
    #
    adantr
    @24
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    @31
    @3
    lcfl9a.h
    lcfl9a.o
    lcfl9a.u
    lcfl9a.v
    @15
    @32
    wph
    @14
    @23
    lcfl9a.k
    adantr
    @24
    cX
    cV
    wcel
    #
    @21
    cX
    cV
    @12
    cdif
    wcel
    wph
    @34
    @23
    lcfl9a.x
    adantr
    wph
    @21
    @22
    simprl
    cX
    cV
    @3
    eldifsn
    sylanbrc
    dochsnshp
    @24
    @22
    @0
    @31
    wcel
    #
    wph
    @21
    @22
    simprr
    wph
    @22
    @35
    wb
    @23
    wph
    cF
    cG
    @31
    cL
    cV
    cU
    lcfl9a.v
    @32
    lcfl9a.f
    lcfl9a.l
    @33
    lcfl9a.g
    lkrshp4
    adantr
    mpbid
    lshpcmp
    mpbid
    #
    fveq2d
    fveq2d
    @36
    3eqtr3d
    pm2.61da2ne
end
