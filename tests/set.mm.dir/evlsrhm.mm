include "wcel.mm"
include "ccrg.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "crh.mm"
include "co.mm"
include "cascl.mm"
include "ccom.mm"
include "cmap.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "wceq.mm"
include "cmvr.mm"
include "wa.mm"
include "eqid.mm"
include "evlsval2.mm"
include "simpld.mm"

theorem evlsrhm
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cI: class I
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume evlsrhm.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlsrhm.w: |- W = ( I mPoly U )
  assume evlsrhm.u: |- U = ( S |`s R )
  assume evlsrhm.t: |- T = ( S ^s ( B ^m I ) )
  assume evlsrhm.b: |- B = ( Base ` S )


  assert |- ( ( I e. V /\ S e. CRing /\ R e. ( SubRing ` S ) ) -> Q e. ( W RingHom T ) )

  proof
    cI
    cV
    wcel
    cS
    ccrg
    wcel
    cR
    cS
    csubrg
    cfv
    wcel
    w3a
    cQ
    cW
    cT
    crh
    co
    wcel
    cQ
    cW
    cascl
    cfv
    #
    ccom
    vx
    cR
    cB
    cI
    cmap
    co
    #
    vx
    cv
    #
    csn
    cxp
    cmpt
    #
    wceq
    cQ
    cI
    cU
    cmvr
    co
    #
    ccom
    vx
    cI
    vy
    @1
    @2
    vy
    cv
    cfv
    cmpt
    cmpt
    #
    wceq
    wa
    vx
    @0
    cB
    cQ
    cR
    cS
    cT
    cU
    vy
    cI
    @4
    cW
    @3
    @5
    cV
    evlsrhm.q
    evlsrhm.w
    @4
    eqid
    evlsrhm.u
    evlsrhm.t
    evlsrhm.b
    @0
    eqid
    @3
    eqid
    @5
    eqid
    evlsval2
    simpld
end
