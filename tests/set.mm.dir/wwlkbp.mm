include "cwwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cword.mm"
include "elfvex.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "iswwlks.mm"
include "simp2bi.mm"
include "jca.mm"

theorem wwlkbp
  let cG: class G
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume wwlkbp.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( WWalks ` G ) -> ( G e. _V /\ W e. Word V ) )

  proof
    cW
    cG
    cwwlks
    cfv
    wcel
    #
    cG
    cvv
    wcel
    cW
    cV
    cword
    wcel
    #
    cW
    cG
    cwwlks
    elfvex
    @0
    cW
    c0
    wne
    @1
    vi
    cv
    #
    cW
    cfv
    @2
    c1
    caddc
    co
    cW
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cW
    chash
    cfv
    c1
    cmin
    co
    cfzo
    co
    wral
    vi
    @3
    cG
    cV
    cW
    wwlkbp.v
    @3
    eqid
    iswwlks
    simp2bi
    jca
end
