include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "wceq.mm"
include "tgrpopr.mm"
include "3adant3.mm"
include "oveqd.mm"
include "cvv.mm"
include "simp3l.mm"
include "simp3r.mm"
include "coexg.mm"
include "3ad2ant3.mm"
include "coeq1.mm"
include "coeq2.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem tgrpov
  let c.pl: class .+
  let cT: class T
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let cB: class B
  assume tgrpset.h: |- H = ( LHyp ` K )
  assume tgrpset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tgrpset.g: |- G = ( ( TGrp ` K ) ` W )
  assume tgrp.o: |- .+ = ( +g ` G )


  assert |- ( ( K e. V /\ W e. H /\ ( X e. T /\ Y e. T ) ) -> ( X .+ Y ) = ( X o. Y ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    cX
    cT
    wcel
    #
    cY
    cT
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    cX
    cY
    vf
    vg
    cT
    cT
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    cmpt2
    #
    co
    #
    cX
    cY
    ccom
    #
    @5
    c.pl
    @9
    cX
    cY
    @0
    @1
    c.pl
    @9
    wceq
    @4
    c.pl
    cT
    vf
    vg
    cG
    cH
    cK
    cV
    cW
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrp.o
    tgrpopr
    3adant3
    oveqd
    @5
    @2
    @3
    @11
    cvv
    wcel
    #
    @10
    @11
    wceq
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @2
    @3
    simp3r
    @4
    @0
    @12
    @1
    cX
    cY
    cT
    cT
    coexg
    3ad2ant3
    vf
    vg
    cX
    cY
    cT
    cT
    @8
    @11
    @9
    cX
    @7
    ccom
    cvv
    @6
    cX
    @7
    coeq1
    @7
    cY
    cX
    coeq2
    @9
    eqid
    ovmpt2g
    syl3anc
    eqtrd
end
