include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "csn.mm"
include "wne.mm"
include "lsatcv1.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "co.mm"
include "clvec.mm"
include "clmod.mm"
include "wcel.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lcvpss.mm"
include "lsatcvat.mm"

theorem lsatcvat2
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  assume lsatcvat2.s: |- S = ( LSubSp ` W )
  assume lsatcvat2.p: |- .(+) = ( LSSum ` W )
  assume lsatcvat2.a: |- A = ( LSAtoms ` W )
  assume lsatcvat2.c: |- C = ( <oL ` W )
  assume lsatcvat2.w: |- ( ph -> W e. LVec )
  assume lsatcvat2.u: |- ( ph -> U e. S )
  assume lsatcvat2.q: |- ( ph -> Q e. A )
  assume lsatcvat2.r: |- ( ph -> R e. A )
  assume lsatcvat2.n: |- ( ph -> Q =/= R )
  assume lsatcvat2.l: |- ( ph -> U C ( Q .(+) R ) )


  assert |- ( ph -> U e. A )

  proof
    wph
    cA
    c.po
    cQ
    cR
    cS
    cU
    cW
    cW
    c0g
    cfv
    #
    @0
    eqid
    #
    lsatcvat2.s
    lsatcvat2.p
    lsatcvat2.a
    lsatcvat2.w
    lsatcvat2.u
    lsatcvat2.q
    lsatcvat2.r
    wph
    cU
    @0
    csn
    #
    wne
    cQ
    cR
    wne
    lsatcvat2.n
    wph
    cU
    @2
    cQ
    cR
    wph
    cA
    cC
    c.po
    cQ
    cR
    cS
    cU
    cW
    @0
    @1
    lsatcvat2.p
    lsatcvat2.s
    lsatcvat2.a
    lsatcvat2.c
    lsatcvat2.w
    lsatcvat2.u
    lsatcvat2.q
    lsatcvat2.r
    lsatcvat2.l
    lsatcv1
    necon3bid
    mpbird
    wph
    cC
    cS
    cU
    cQ
    cR
    c.po
    co
    #
    cW
    clvec
    lsatcvat2.s
    lsatcvat2.c
    lsatcvat2.w
    lsatcvat2.u
    wph
    cW
    clmod
    wcel
    #
    cQ
    cS
    wcel
    cR
    cS
    wcel
    @3
    cS
    wcel
    wph
    cW
    clvec
    wcel
    @4
    lsatcvat2.w
    cW
    lveclmod
    syl
    #
    wph
    cA
    cS
    cQ
    cW
    lsatcvat2.s
    lsatcvat2.a
    @5
    lsatcvat2.q
    lsatlssel
    wph
    cA
    cS
    cR
    cW
    lsatcvat2.s
    lsatcvat2.a
    @5
    lsatcvat2.r
    lsatlssel
    c.po
    cS
    cQ
    cR
    cW
    lsatcvat2.s
    lsatcvat2.p
    lsmcl
    syl3anc
    lsatcvat2.l
    lcvpss
    lsatcvat
end
