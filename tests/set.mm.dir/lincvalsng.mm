include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "cpw.mm"
include "wceq.mm"
include "simp1.mm"
include "cvv.mm"
include "simp2.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "fvexd.mm"
include "eqid.mm"
include "mapsnop.mm"
include "syl3anc.mm"
include "snelpwi.mm"
include "eleq2s.mm"
include "3ad2ant2.mm"
include "lincval.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "fvsng.mm"
include "3adant1.mm"
include "oveq1d.mm"
include "lmodvscl.mm"
include "3com23.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "3eqtrd.mm"

theorem lincvalsng
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cM: class M
  let cV: class V
  let cY: class Y
  let vv: setvar v
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume lincvalsn.b: |- B = ( Base ` M )
  assume lincvalsn.s: |- S = ( Scalar ` M )
  assume lincvalsn.r: |- R = ( Base ` S )
  assume lincvalsn.t: |- .x. = ( .s ` M )


  assert |- ( ( M e. LMod /\ V e. B /\ Y e. R ) -> ( { <. V , Y >. } ( linC ` M ) { V } ) = ( Y .x. V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    wcel
    #
    cY
    cR
    wcel
    #
    w3a
    #
    cV
    cY
    cop
    csn
    #
    cV
    csn
    #
    cM
    clinc
    cfv
    co
    #
    cM
    vv
    @5
    vv
    cv
    #
    @4
    cfv
    #
    @7
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cV
    @4
    cfv
    #
    cV
    @9
    co
    #
    cY
    cV
    c.x
    co
    @3
    @0
    @4
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @5
    cmap
    co
    wcel
    #
    @5
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    @6
    @11
    wceq
    @0
    @1
    @2
    simp1
    @3
    @1
    cY
    @15
    wcel
    #
    @15
    cvv
    wcel
    @16
    @0
    @1
    @2
    simp2
    #
    @2
    @0
    @19
    @1
    @2
    @19
    cR
    @15
    cY
    cR
    cS
    cbs
    cfv
    @15
    lincvalsn.r
    cS
    @14
    cbs
    lincvalsn.s
    fveq2i
    eqtri
    eleq2i
    biimpi
    3ad2ant3
    @3
    @14
    cbs
    fvexd
    @15
    @4
    cB
    cvv
    cV
    cY
    @4
    eqid
    mapsnop
    syl3anc
    @1
    @0
    @18
    @2
    @18
    cV
    @17
    cB
    cV
    @17
    snelpwi
    lincvalsn.b
    eleq2s
    3ad2ant2
    vv
    @4
    cM
    @5
    clmod
    lincval
    syl3anc
    @3
    cM
    cmnd
    wcel
    #
    @1
    @13
    cB
    wcel
    @11
    @13
    wceq
    @0
    @1
    @21
    @2
    @0
    cM
    cgrp
    wcel
    @21
    cM
    lmodgrp
    cM
    grpmnd
    syl
    3ad2ant1
    @20
    @3
    @13
    cY
    cV
    @9
    co
    #
    cB
    @3
    @12
    cY
    cV
    @9
    @1
    @2
    @12
    cY
    wceq
    @0
    cV
    cY
    cB
    cR
    fvsng
    3adant1
    #
    oveq1d
    @0
    @2
    @1
    @22
    cB
    wcel
    cY
    @9
    cS
    cR
    cB
    cM
    cV
    lincvalsn.b
    lincvalsn.s
    @9
    eqid
    lincvalsn.r
    lmodvscl
    3com23
    eqeltrd
    @10
    cB
    @13
    vv
    cM
    cV
    cB
    lincvalsn.b
    @7
    cV
    wceq
    #
    @8
    @12
    @7
    cV
    @9
    @7
    cV
    @4
    fveq2
    @24
    id
    oveq12d
    gsumsn
    syl3anc
    @3
    @12
    cY
    cV
    cV
    @9
    c.x
    @9
    c.x
    wceq
    @3
    c.x
    @9
    lincvalsn.t
    eqcomi
    a1i
    @23
    @3
    cV
    eqidd
    oveq123d
    3eqtrd
end
