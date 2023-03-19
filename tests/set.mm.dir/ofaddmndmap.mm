include "cmnd.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "w3a.mm"
include "cof.mm"
include "wf.mm"
include "cv.mm"
include "simpl1.mm"
include "simprl.mm"
include "simprr.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "elmapi.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "simp2.mm"
include "inidm.mm"
include "off.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem ofaddmndmap
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cM: class M
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume ofaddmndmap.r: |- R = ( Base ` M )
  assume ofaddmndmap.p: |- .+ = ( +g ` M )


  assert |- ( ( M e. Mnd /\ V e. Y /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) ) ) -> ( A oF .+ B ) e. ( R ^m V ) )

  proof
    cM
    cmnd
    wcel
    #
    cV
    cY
    wcel
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    cB
    @2
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    c.pl
    cof
    co
    #
    @2
    wcel
    #
    cV
    cR
    @7
    wf
    #
    @6
    vx
    vy
    cV
    cV
    cV
    c.pl
    cR
    cR
    cR
    cA
    cB
    cY
    cY
    @6
    vx
    cv
    #
    cR
    wcel
    #
    vy
    cv
    #
    cR
    wcel
    #
    wa
    #
    wa
    @0
    @11
    @13
    @10
    @12
    c.pl
    co
    cR
    wcel
    @0
    @1
    @5
    @14
    simpl1
    @6
    @11
    @13
    simprl
    @6
    @11
    @13
    simprr
    cR
    c.pl
    cM
    @10
    @12
    ofaddmndmap.r
    ofaddmndmap.p
    mndcl
    syl3anc
    @5
    @0
    cV
    cR
    cA
    wf
    #
    @1
    @3
    @15
    @4
    cA
    cR
    cV
    elmapi
    adantr
    3ad2ant3
    @5
    @0
    cV
    cR
    cB
    wf
    #
    @1
    @4
    @16
    @3
    cB
    cR
    cV
    elmapi
    adantl
    3ad2ant3
    @0
    @1
    @5
    simp2
    #
    @17
    cV
    inidm
    off
    @6
    cR
    cvv
    wcel
    @1
    @8
    @9
    wb
    cR
    cM
    cbs
    cfv
    cvv
    ofaddmndmap.r
    cM
    cbs
    fvex
    eqeltri
    @17
    cR
    cV
    @7
    cvv
    cY
    elmapg
    sylancr
    mpbird
end
