include "cv.mm"
include "co.mm"
include "cfv.mm"
include "csubg.mm"
include "wcel.mm"
include "wss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "chlt.mm"
include "wa.mm"
include "lssss.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lsmless12.mm"
include "syl22anc.mm"
include "sstrd.mm"

theorem dochexmidlem2
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume dochexmidlem1.h: |- H = ( LHyp ` K )
  assume dochexmidlem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmidlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmidlem1.v: |- V = ( Base ` U )
  assume dochexmidlem1.s: |- S = ( LSubSp ` U )
  assume dochexmidlem1.n: |- N = ( LSpan ` U )
  assume dochexmidlem1.p: |- .(+) = ( LSSum ` U )
  assume dochexmidlem1.a: |- A = ( LSAtoms ` U )
  assume dochexmidlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmidlem1.x: |- ( ph -> X e. S )
  assume dochexmidlem2.pp: |- ( ph -> p e. A )
  assume dochexmidlem2.qq: |- ( ph -> q e. A )
  assume dochexmidlem2.rr: |- ( ph -> r e. A )
  assume dochexmidlem2.ql: |- ( ph -> q C_ ( ._|_ ` X ) )
  assume dochexmidlem2.rl: |- ( ph -> r C_ X )
  assume dochexmidlem2.pl: |- ( ph -> p C_ ( r .(+) q ) )


  assert |- ( ph -> p C_ ( X .(+) ( ._|_ ` X ) ) )

  proof
    wph
    vp
    cv
    vr
    cv
    #
    vq
    cv
    #
    c.po
    co
    #
    cX
    cX
    c.pe
    cfv
    #
    c.po
    co
    #
    dochexmidlem2.pl
    wph
    cX
    cU
    csubg
    cfv
    #
    wcel
    @3
    @5
    wcel
    @0
    cX
    wss
    @1
    @3
    wss
    @2
    @4
    wss
    wph
    cS
    @5
    cX
    wph
    cU
    clmod
    wcel
    cS
    @5
    wss
    wph
    cU
    cH
    cK
    cW
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.k
    dvhlmod
    cS
    cU
    dochexmidlem1.s
    lsssssubg
    syl
    #
    dochexmidlem1.x
    sseldd
    wph
    cS
    @5
    @3
    @6
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cV
    wss
    #
    @3
    cS
    wcel
    dochexmidlem1.k
    wph
    cX
    cS
    wcel
    @7
    dochexmidlem1.x
    cS
    cX
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lssss
    syl
    cS
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.o
    dochlss
    syl2anc
    sseldd
    dochexmidlem2.rl
    dochexmidlem2.ql
    c.po
    @0
    cX
    @1
    @3
    cU
    dochexmidlem1.p
    lsmless12
    syl22anc
    sstrd
end
