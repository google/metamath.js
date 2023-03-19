include "coml.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "clat.mm"
include "omllat.mm"
include "eqid.mm"
include "latref.mm"
include "sylan.mm"
include "wi.mm"
include "lecmtN.mm"
include "3anidm23.mm"
include "mpd.mm"

theorem cmtidN
  let cB: class B
  let cC: class C
  let cK: class K
  let cX: class X
  assume cmtid.b: |- B = ( Base ` K )
  assume cmtid.c: |- C = ( cm ` K )


  assert |- ( ( K e. OML /\ X e. B ) -> X C X )

  proof
    cK
    coml
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cX
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cX
    cC
    wbr
    #
    @0
    cK
    clat
    wcel
    @1
    @3
    cK
    omllat
    cB
    cK
    @2
    cX
    cmtid.b
    @2
    eqid
    #
    latref
    sylan
    @0
    @1
    @3
    @4
    wi
    cB
    cC
    cK
    @2
    cX
    cX
    cmtid.b
    @5
    cmtid.c
    lecmtN
    3anidm23
    mpd
end
