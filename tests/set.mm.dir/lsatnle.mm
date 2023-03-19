include "wss.mm"
include "wn.mm"
include "clsm.mm"
include "cfv.mm"
include "co.mm"
include "clcv.mm"
include "wbr.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "eqid.mm"
include "lcv1.mm"
include "lcvp.mm"
include "bitr4d.mm"

theorem lsatnle
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsatnle.o: |- .0. = ( 0g ` W )
  assume lsatnle.s: |- S = ( LSubSp ` W )
  assume lsatnle.a: |- A = ( LSAtoms ` W )
  assume lsatnle.w: |- ( ph -> W e. LVec )
  assume lsatnle.u: |- ( ph -> U e. S )
  assume lsatnle.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( -. Q C_ U <-> ( U i^i Q ) = { .0. } ) )

  proof
    wph
    cQ
    cU
    wss
    wn
    cU
    cU
    cQ
    cW
    clsm
    cfv
    #
    co
    cW
    clcv
    cfv
    #
    wbr
    cU
    cQ
    cin
    c.0
    csn
    wceq
    wph
    cA
    @1
    @0
    cQ
    cS
    cU
    cW
    lsatnle.s
    @0
    eqid
    #
    lsatnle.a
    @1
    eqid
    #
    lsatnle.w
    lsatnle.u
    lsatnle.q
    lcv1
    wph
    cA
    @1
    @0
    cQ
    cS
    cU
    cW
    c.0
    lsatnle.s
    @2
    lsatnle.o
    lsatnle.a
    @3
    lsatnle.w
    lsatnle.u
    lsatnle.q
    lcvp
    bitr4d
end
