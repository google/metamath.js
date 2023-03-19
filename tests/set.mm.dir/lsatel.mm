include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "clss.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lspsnel5a.mm"
include "cbs.mm"
include "wne.mm"
include "lssel.mm"
include "syl2anc.mm"
include "lsatlspsn2.mm"
include "syl3anc.mm"
include "lsatcmp.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem lsatel
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lsatel.o: |- .0. = ( 0g ` W )
  assume lsatel.n: |- N = ( LSpan ` W )
  assume lsatel.a: |- A = ( LSAtoms ` W )
  assume lsatel.w: |- ( ph -> W e. LVec )
  assume lsatel.u: |- ( ph -> U e. A )
  assume lsatel.x: |- ( ph -> X e. U )
  assume lsatel.e: |- ( ph -> X =/= .0. )


  assert |- ( ph -> U = ( N ` { X } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cU
    wph
    @0
    cU
    wss
    @0
    cU
    wceq
    wph
    cW
    clss
    cfv
    #
    cU
    cN
    cW
    cX
    @1
    eqid
    #
    lsatel.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    #
    lsatel.w
    cW
    lveclmod
    syl
    #
    wph
    cA
    @1
    cU
    cW
    @2
    lsatel.a
    @4
    lsatel.u
    lsatlssel
    #
    lsatel.x
    lspsnel5a
    wph
    cA
    @0
    cU
    cW
    lsatel.a
    lsatel.w
    wph
    @3
    cX
    cW
    cbs
    cfv
    #
    wcel
    #
    cX
    c.0
    wne
    @0
    cA
    wcel
    @4
    wph
    cU
    @1
    wcel
    cX
    cU
    wcel
    @7
    @5
    lsatel.x
    @1
    cU
    @6
    cW
    cX
    @6
    eqid
    #
    @2
    lssel
    syl2anc
    lsatel.e
    cA
    cN
    @6
    cW
    cX
    c.0
    @8
    lsatel.n
    lsatel.o
    lsatel.a
    lsatlspsn2
    syl3anc
    lsatel.u
    lsatcmp
    mpbid
    eqcomd
end
