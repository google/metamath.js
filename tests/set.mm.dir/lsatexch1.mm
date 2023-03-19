include "clss.mm"
include "cfv.mm"
include "c0g.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "wne.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "necomd.mm"
include "lsatnem0.mm"
include "mpbid.mm"
include "lsatexch.mm"

theorem lsatexch1
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cW: class W
  assume lsatexch1.p: |- .(+) = ( LSSum ` W )
  assume lsatexch1.a: |- A = ( LSAtoms ` W )
  assume lsatexch1.w: |- ( ph -> W e. LVec )
  assume lsatexch1.u: |- ( ph -> Q e. A )
  assume lsatexch1.q: |- ( ph -> R e. A )
  assume lsatexch1.r: |- ( ph -> S e. A )
  assume lsatexch1.l: |- ( ph -> Q C_ ( S .(+) R ) )
  assume lsatexch1.z: |- ( ph -> Q =/= S )


  assert |- ( ph -> R C_ ( S .(+) Q ) )

  proof
    wph
    cA
    c.po
    cQ
    cR
    cW
    clss
    cfv
    #
    cS
    cW
    cW
    c0g
    cfv
    #
    @0
    eqid
    #
    lsatexch1.p
    @1
    eqid
    #
    lsatexch1.a
    lsatexch1.w
    wph
    cA
    @0
    cS
    cW
    @2
    lsatexch1.a
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    lsatexch1.w
    cW
    lveclmod
    syl
    lsatexch1.r
    lsatlssel
    lsatexch1.u
    lsatexch1.q
    lsatexch1.l
    wph
    cS
    cQ
    wne
    cS
    cQ
    cin
    @1
    csn
    wceq
    wph
    cQ
    cS
    lsatexch1.z
    necomd
    wph
    cA
    cS
    cQ
    cW
    @1
    @3
    lsatexch1.a
    lsatexch1.w
    lsatexch1.r
    lsatexch1.u
    lsatnem0
    mpbid
    lsatexch
end
