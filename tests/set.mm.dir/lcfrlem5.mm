include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "syl6eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "wa.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "ad2antrr.mm"
include "chlt.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "lssss.mm"
include "syl.mm"
include "ldualvbase.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "adantr.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "simpr.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "sylibr.mm"
include "syl6eleqr.mm"

theorem lcfrlem5
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcfrlem5.h: |- H = ( LHyp ` K )
  assume lcfrlem5.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem5.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem5.v: |- V = ( Base ` U )
  assume lcfrlem5.f: |- F = ( LFnl ` U )
  assume lcfrlem5.l: |- L = ( LKer ` U )
  assume lcfrlem5.d: |- D = ( LDual ` U )
  assume lcfrlem5.s: |- S = ( LSubSp ` D )
  assume lcfrlem5.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem5.r: |- ( ph -> R e. S )
  assume lcfrlem5.q: |- Q = U_ f e. R ( ._|_ ` ( L ` f ) )
  assume lcfrlem5.x: |- ( ph -> X e. Q )
  assume lcfrlem5.c: |- C = ( Scalar ` U )
  assume lcfrlem5.b: |- B = ( Base ` C )
  assume lcfrlem5.t: |- .x. = ( .s ` U )
  assume lcfrlem5.a: |- ( ph -> A e. B )

  disjoint A f
  disjoint .x. f
  disjoint X f
  disjoint f ph
  assert |- ( ph -> ( A .x. X ) e. Q )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    vf
    cR
    vf
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    ciun
    #
    cQ
    wph
    @0
    @3
    wcel
    #
    vf
    cR
    wrex
    #
    @0
    @4
    wcel
    wph
    cX
    @3
    wcel
    #
    vf
    cR
    wrex
    #
    @6
    wph
    cX
    @4
    wcel
    @8
    wph
    cX
    cQ
    @4
    lcfrlem5.x
    lcfrlem5.q
    syl6eleq
    vf
    cX
    cR
    @3
    eliun
    sylib
    wph
    @7
    @5
    vf
    cR
    wph
    @1
    cR
    wcel
    #
    wa
    #
    @7
    @5
    @10
    @7
    wa
    #
    cU
    clmod
    wcel
    #
    @3
    cU
    clss
    cfv
    #
    wcel
    #
    cA
    cB
    wcel
    #
    @7
    @5
    wph
    @12
    @9
    @7
    wph
    cU
    cH
    cK
    cW
    lcfrlem5.h
    lcfrlem5.u
    lcfrlem5.k
    dvhlmod
    #
    ad2antrr
    #
    @11
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    cV
    wss
    @14
    wph
    @18
    @9
    @7
    lcfrlem5.k
    ad2antrr
    @11
    cF
    @1
    cL
    cV
    cU
    lcfrlem5.v
    lcfrlem5.f
    lcfrlem5.l
    @17
    @10
    @1
    cF
    wcel
    @7
    wph
    cR
    cF
    @1
    wph
    cR
    cD
    cbs
    cfv
    #
    cF
    wph
    cR
    cS
    wcel
    cR
    @19
    wss
    lcfrlem5.r
    cS
    cR
    @19
    cD
    @19
    eqid
    #
    lcfrlem5.s
    lssss
    syl
    wph
    cD
    cF
    @19
    cU
    clmod
    lcfrlem5.f
    lcfrlem5.d
    @20
    @16
    ldualvbase
    sseqtrd
    sselda
    adantr
    lkrssv
    @13
    cU
    cH
    cK
    c.pe
    cV
    cW
    @2
    lcfrlem5.h
    lcfrlem5.u
    lcfrlem5.v
    @13
    eqid
    #
    lcfrlem5.o
    dochlss
    syl2anc
    wph
    @15
    @9
    @7
    lcfrlem5.a
    ad2antrr
    @10
    @7
    simpr
    cB
    @13
    c.x
    @3
    cC
    cU
    cA
    cX
    lcfrlem5.c
    lcfrlem5.t
    lcfrlem5.b
    @21
    lssvscl
    syl22anc
    ex
    reximdva
    mpd
    vf
    @0
    cR
    @3
    eliun
    sylibr
    lcfrlem5.q
    syl6eleqr
end
