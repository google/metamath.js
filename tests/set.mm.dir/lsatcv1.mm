include "csn.mm"
include "wceq.mm"
include "co.mm"
include "wbr.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "lsatcv0eq.mm"
include "sylibd.mm"
include "wa.mm"
include "adantr.mm"
include "clvec.mm"
include "wcel.mm"
include "oveq1.mm"
include "csubg.mm"
include "cfv.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "lsmidm.mm"
include "sylan9eqr.mm"
include "eqeltrd.mm"
include "lsatcveq0.mm"
include "mpbid.mm"
include "ex.mm"
include "impbid.mm"

theorem lsatcv1
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsatcv1.o: |- .0. = ( 0g ` W )
  assume lsatcv1.p: |- .(+) = ( LSSum ` W )
  assume lsatcv1.s: |- S = ( LSubSp ` W )
  assume lsatcv1.a: |- A = ( LSAtoms ` W )
  assume lsatcv1.c: |- C = ( <oL ` W )
  assume lsatcv1.w: |- ( ph -> W e. LVec )
  assume lsatcv1.u: |- ( ph -> U e. S )
  assume lsatcv1.q: |- ( ph -> Q e. A )
  assume lsatcv1.r: |- ( ph -> R e. A )
  assume lsatcv1.l: |- ( ph -> U C ( Q .(+) R ) )


  assert |- ( ph -> ( U = { .0. } <-> Q = R ) )

  proof
    wph
    cU
    c.0
    csn
    #
    wceq
    #
    cQ
    cR
    wceq
    #
    wph
    @1
    @0
    cQ
    cR
    c.po
    co
    #
    cC
    wbr
    #
    @2
    wph
    cU
    @3
    cC
    wbr
    #
    @1
    @4
    lsatcv1.l
    cU
    @0
    @3
    cC
    breq1
    syl5ibcom
    wph
    cA
    cC
    c.po
    cQ
    cR
    cW
    c.0
    lsatcv1.o
    lsatcv1.p
    lsatcv1.a
    lsatcv1.c
    lsatcv1.w
    lsatcv1.q
    lsatcv1.r
    lsatcv0eq
    sylibd
    wph
    @2
    @1
    wph
    @2
    wa
    #
    @5
    @1
    wph
    @5
    @2
    lsatcv1.l
    adantr
    @6
    cA
    cC
    @3
    cS
    cU
    cW
    c.0
    lsatcv1.o
    lsatcv1.s
    lsatcv1.a
    lsatcv1.c
    wph
    cW
    clvec
    wcel
    #
    @2
    lsatcv1.w
    adantr
    wph
    cU
    cS
    wcel
    @2
    lsatcv1.u
    adantr
    @6
    @3
    cR
    cA
    @2
    wph
    @3
    cR
    cR
    c.po
    co
    #
    cR
    cQ
    cR
    cR
    c.po
    oveq1
    wph
    cR
    cW
    csubg
    cfv
    wcel
    #
    @8
    cR
    wceq
    wph
    cW
    clmod
    wcel
    #
    cR
    cS
    wcel
    @9
    wph
    @7
    @10
    lsatcv1.w
    cW
    lveclmod
    syl
    #
    wph
    cA
    cS
    cR
    cW
    lsatcv1.s
    lsatcv1.a
    @11
    lsatcv1.r
    lsatlssel
    cS
    cR
    cW
    lsatcv1.s
    lsssubg
    syl2anc
    c.po
    cR
    cW
    lsatcv1.p
    lsmidm
    syl
    sylan9eqr
    wph
    cR
    cA
    wcel
    @2
    lsatcv1.r
    adantr
    eqeltrd
    lsatcveq0
    mpbid
    ex
    impbid
end
