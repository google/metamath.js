include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cmpl.mm"
include "crh.mm"
include "csubrg.mm"
include "cfv.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "subrgid.mm"
include "syl.mm"
include "evlval.mm"
include "eqid.mm"
include "evlsrhm.mm"
include "mpd3an3.mm"
include "wceq.mm"
include "ressid.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eleqtrd.mm"

theorem evlrhm
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cI: class I
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vr: setvar r
  assume evlval.q: |- Q = ( I eval R )
  assume evlval.b: |- B = ( Base ` R )
  assume evlrhm.w: |- W = ( I mPoly R )
  assume evlrhm.t: |- T = ( R ^s ( B ^m I ) )


  assert |- ( ( I e. V /\ R e. CRing ) -> Q e. ( W RingHom T ) )

  proof
    cI
    cV
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cQ
    cI
    cR
    cB
    cress
    co
    #
    cmpl
    co
    #
    cT
    crh
    co
    #
    cW
    cT
    crh
    co
    @0
    @1
    cB
    cR
    csubrg
    cfv
    wcel
    #
    cQ
    @5
    wcel
    @2
    cR
    crg
    wcel
    #
    @6
    @1
    @7
    @0
    cR
    crngring
    adantl
    cB
    cR
    evlval.b
    subrgid
    syl
    cB
    cQ
    cB
    cR
    cT
    @3
    cI
    cV
    @4
    cB
    cQ
    cR
    cI
    evlval.q
    evlval.b
    evlval
    @4
    eqid
    @3
    eqid
    evlrhm.t
    evlval.b
    evlsrhm
    mpd3an3
    @2
    @4
    cW
    cT
    crh
    @2
    @4
    cI
    cR
    cmpl
    co
    cW
    @2
    @3
    cR
    cI
    cmpl
    @1
    @3
    cR
    wceq
    @0
    cB
    cR
    ccrg
    evlval.b
    ressid
    adantl
    oveq2d
    evlrhm.w
    syl6eqr
    oveq1d
    eleqtrd
end
