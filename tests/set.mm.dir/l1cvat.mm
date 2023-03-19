include "co.mm"
include "cin.mm"
include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wceq.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodabl.mm"
include "wss.mm"
include "lsssssubg.mm"
include "lsatlssel.mm"
include "sseldd.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "ineq1d.mm"
include "incom.mm"
include "syl6eq.mm"
include "necomd.mm"
include "lsatssv.mm"
include "l1cvpat.mm"
include "sseqtr4d.mm"
include "lsatcvat3.mm"
include "eqeltrd.mm"

theorem l1cvat
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  assume l1cvat.v: |- V = ( Base ` W )
  assume l1cvat.s: |- S = ( LSubSp ` W )
  assume l1cvat.p: |- .(+) = ( LSSum ` W )
  assume l1cvat.a: |- A = ( LSAtoms ` W )
  assume l1cvat.c: |- C = ( <oL ` W )
  assume l1cvat.w: |- ( ph -> W e. LVec )
  assume l1cvat.u: |- ( ph -> U e. S )
  assume l1cvat.q: |- ( ph -> Q e. A )
  assume l1cvat.r: |- ( ph -> R e. A )
  assume l1cvat.n: |- ( ph -> Q =/= R )
  assume l1cvat.l: |- ( ph -> U C V )
  assume l1cvat.m: |- ( ph -> -. Q C_ U )


  assert |- ( ph -> ( ( Q .(+) R ) i^i U ) e. A )

  proof
    wph
    cQ
    cR
    c.po
    co
    #
    cU
    cin
    #
    cU
    cR
    cQ
    c.po
    co
    #
    cin
    #
    cA
    wph
    @1
    @2
    cU
    cin
    @3
    wph
    @0
    @2
    cU
    wph
    cW
    cabl
    wcel
    #
    cQ
    cW
    csubg
    cfv
    #
    wcel
    cR
    @5
    wcel
    @0
    @2
    wceq
    wph
    cW
    clmod
    wcel
    #
    @4
    wph
    cW
    clvec
    wcel
    @6
    l1cvat.w
    cW
    lveclmod
    syl
    #
    cW
    lmodabl
    syl
    wph
    cS
    @5
    cQ
    wph
    @6
    cS
    @5
    wss
    @7
    cS
    cW
    l1cvat.s
    lsssssubg
    syl
    #
    wph
    cA
    cS
    cQ
    cW
    l1cvat.s
    l1cvat.a
    @7
    l1cvat.q
    lsatlssel
    sseldd
    wph
    cS
    @5
    cR
    @8
    wph
    cA
    cS
    cR
    cW
    l1cvat.s
    l1cvat.a
    @7
    l1cvat.r
    lsatlssel
    sseldd
    c.po
    cQ
    cR
    cW
    l1cvat.p
    lsmcom
    syl3anc
    ineq1d
    @2
    cU
    incom
    syl6eq
    wph
    cA
    c.po
    cR
    cQ
    cS
    cU
    cW
    l1cvat.s
    l1cvat.p
    l1cvat.a
    l1cvat.w
    l1cvat.u
    l1cvat.r
    l1cvat.q
    wph
    cQ
    cR
    l1cvat.n
    necomd
    l1cvat.m
    wph
    cR
    cV
    cU
    cQ
    c.po
    co
    wph
    cA
    cR
    cV
    cW
    l1cvat.v
    l1cvat.a
    @7
    l1cvat.r
    lsatssv
    wph
    cA
    cC
    c.po
    cQ
    cS
    cU
    cV
    cW
    l1cvat.v
    l1cvat.s
    l1cvat.p
    l1cvat.a
    l1cvat.c
    l1cvat.w
    l1cvat.u
    l1cvat.q
    l1cvat.l
    l1cvat.m
    l1cvpat
    sseqtr4d
    lsatcvat3
    eqeltrd
end
