include "wss.mm"
include "wn.mm"
include "wne.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "lsatcmp.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "necon3bbid.mm"
include "clss.mm"
include "cfv.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lsatnle.mm"
include "bitr3d.mm"

theorem lsatnem0
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cW: class W
  let c.0: class .0.
  assume lsatnem0.o: |- .0. = ( 0g ` W )
  assume lsatnem0.a: |- A = ( LSAtoms ` W )
  assume lsatnem0.w: |- ( ph -> W e. LVec )
  assume lsatnem0.q: |- ( ph -> Q e. A )
  assume lsatnem0.r: |- ( ph -> R e. A )


  assert |- ( ph -> ( Q =/= R <-> ( Q i^i R ) = { .0. } ) )

  proof
    wph
    cR
    cQ
    wss
    #
    wn
    cQ
    cR
    wne
    cQ
    cR
    cin
    c.0
    csn
    wceq
    wph
    @0
    cQ
    cR
    wph
    @0
    cR
    cQ
    wceq
    cQ
    cR
    wceq
    wph
    cA
    cR
    cQ
    cW
    lsatnem0.a
    lsatnem0.w
    lsatnem0.r
    lsatnem0.q
    lsatcmp
    cR
    cQ
    eqcom
    syl6bb
    necon3bbid
    wph
    cA
    cR
    cW
    clss
    cfv
    #
    cQ
    cW
    c.0
    lsatnem0.o
    @1
    eqid
    #
    lsatnem0.a
    lsatnem0.w
    wph
    cA
    @1
    cQ
    cW
    @2
    lsatnem0.a
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    lsatnem0.w
    cW
    lveclmod
    syl
    lsatnem0.q
    lsatlssel
    lsatnem0.r
    lsatnle
    bitr3d
end
