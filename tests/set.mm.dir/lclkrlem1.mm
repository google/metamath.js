include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "wa.mm"
include "lcfl1lem.mm"
include "sylib.mm"
include "simpld.mm"
include "ldualvscl.mm"
include "c0g.mm"
include "cbs.mm"
include "eqid.mm"
include "dochoc1.mm"
include "adantr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "csn.mm"
include "cxp.mm"
include "csca.mm"
include "clmod.mm"
include "lduallmod.mm"
include "ldualelvbase.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "ldual0.mm"
include "oveq1d.mm"
include "ldual0v.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "lfl0f.mm"
include "syl.mm"
include "lkr0f.mm"
include "mpbiri.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "simprd.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simpr.mm"
include "ldualkrsc.mm"
include "pm2.61dane.mm"
include "sylanbrc.mm"

theorem lclkrlem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume lclkrlem1.h: |- H = ( LHyp ` K )
  assume lclkrlem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem1.f: |- F = ( LFnl ` U )
  assume lclkrlem1.l: |- L = ( LKer ` U )
  assume lclkrlem1.d: |- D = ( LDual ` U )
  assume lclkrlem1.r: |- R = ( Scalar ` U )
  assume lclkrlem1.b: |- B = ( Base ` R )
  assume lclkrlem1.t: |- .x. = ( .s ` D )
  assume lclkrlem1.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lclkrlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem1.x: |- ( ph -> X e. B )
  assume lclkrlem1.g: |- ( ph -> G e. C )

  disjoint F f
  disjoint L f
  disjoint ._|_ f
  disjoint .x. f
  disjoint G f
  disjoint X f
  assert |- ( ph -> ( X .x. G ) e. C )

  proof
    wph
    cX
    cG
    c.x
    co
    #
    cF
    wcel
    @0
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    #
    @0
    cC
    wcel
    wph
    cD
    cR
    c.x
    cF
    cG
    cB
    cU
    cX
    lclkrlem1.f
    lclkrlem1.r
    lclkrlem1.b
    lclkrlem1.d
    lclkrlem1.t
    wph
    cU
    cH
    cK
    cW
    lclkrlem1.h
    lclkrlem1.u
    lclkrlem1.k
    dvhlmod
    #
    lclkrlem1.x
    wph
    cG
    cF
    wcel
    #
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
    @7
    wceq
    #
    wph
    cG
    cC
    wcel
    @6
    @10
    wa
    lclkrlem1.g
    cC
    vf
    cF
    cG
    cL
    c.pe
    lclkrlem1.c
    lcfl1lem
    sylib
    #
    simpld
    #
    ldualvscl
    wph
    @4
    cX
    cR
    c0g
    cfv
    #
    wph
    cX
    @13
    wceq
    #
    wa
    #
    cU
    cbs
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @16
    @3
    @1
    wph
    @18
    @16
    wceq
    @14
    wph
    cU
    cH
    cK
    c.pe
    @16
    cW
    lclkrlem1.h
    lclkrlem1.u
    lclkrlem1.o
    @16
    eqid
    #
    lclkrlem1.k
    dochoc1
    adantr
    @15
    @2
    @17
    c.pe
    @15
    @1
    @16
    c.pe
    @14
    wph
    @1
    @13
    cG
    c.x
    co
    #
    cL
    cfv
    #
    @16
    @14
    @0
    @20
    cL
    cX
    @13
    cG
    c.x
    oveq1
    fveq2d
    wph
    @21
    @16
    @13
    csn
    cxp
    #
    cL
    cfv
    #
    @16
    wph
    @20
    @22
    cL
    wph
    cD
    csca
    cfv
    #
    c0g
    cfv
    #
    cG
    c.x
    co
    #
    cD
    c0g
    cfv
    #
    @20
    @22
    wph
    cD
    clmod
    wcel
    cG
    cD
    cbs
    cfv
    #
    wcel
    @26
    @27
    wceq
    wph
    cD
    cU
    lclkrlem1.d
    @5
    lduallmod
    wph
    cD
    cF
    cG
    @28
    cU
    clmod
    lclkrlem1.f
    lclkrlem1.d
    @28
    eqid
    #
    @5
    @12
    ldualelvbase
    c.x
    @24
    @25
    @28
    cD
    cG
    @27
    @29
    @24
    eqid
    #
    lclkrlem1.t
    @25
    eqid
    #
    @27
    eqid
    #
    lmod0vs
    syl2anc
    wph
    @25
    @13
    cG
    c.x
    wph
    cD
    cR
    @24
    @25
    cU
    @13
    lclkrlem1.r
    @13
    eqid
    #
    lclkrlem1.d
    @30
    @31
    @5
    ldual0
    oveq1d
    wph
    cD
    cR
    @27
    @16
    cU
    @13
    @19
    lclkrlem1.r
    @33
    lclkrlem1.d
    @32
    @5
    ldual0v
    3eqtr3d
    fveq2d
    wph
    @23
    @16
    wceq
    #
    @22
    @22
    wceq
    #
    @22
    eqid
    wph
    cU
    clmod
    wcel
    #
    @22
    cF
    wcel
    #
    @34
    @35
    wb
    @5
    wph
    @36
    @37
    @5
    cR
    cF
    @16
    cU
    @13
    lclkrlem1.r
    @33
    @19
    lclkrlem1.f
    lfl0f
    syl
    cR
    cF
    @22
    cL
    @16
    cU
    @13
    lclkrlem1.r
    @33
    @19
    lclkrlem1.f
    lclkrlem1.l
    lkr0f
    syl2anc
    mpbiri
    eqtrd
    sylan9eqr
    #
    fveq2d
    fveq2d
    @38
    3eqtr4d
    wph
    cX
    @13
    wne
    #
    wa
    #
    @9
    @7
    @3
    @1
    wph
    @10
    @39
    wph
    @6
    @10
    @11
    simprd
    adantr
    @40
    @2
    @8
    c.pe
    @40
    @1
    @7
    c.pe
    @40
    cD
    cR
    c.x
    cF
    cG
    cB
    cL
    cU
    cX
    @13
    lclkrlem1.r
    lclkrlem1.b
    @33
    lclkrlem1.f
    lclkrlem1.l
    lclkrlem1.d
    lclkrlem1.t
    wph
    cU
    clvec
    wcel
    @39
    wph
    cU
    cH
    cK
    cW
    lclkrlem1.h
    lclkrlem1.u
    lclkrlem1.k
    dvhlvec
    adantr
    wph
    @6
    @39
    @12
    adantr
    wph
    cX
    cB
    wcel
    @39
    lclkrlem1.x
    adantr
    wph
    @39
    simpr
    ldualkrsc
    #
    fveq2d
    fveq2d
    @41
    3eqtr4d
    pm2.61dane
    cC
    vf
    cF
    @0
    cL
    c.pe
    lclkrlem1.c
    lcfl1lem
    sylanbrc
end
