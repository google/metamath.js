include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cnm.mm"
include "c0g.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "cgrp.mm"
include "cghm.mm"
include "co.mm"
include "ngpgrp.mm"
include "0ghm.mm"
include "syl2an.mm"
include "0red.mm"
include "0le0.mm"
include "a1i.mm"
include "cv.mm"
include "wne.mm"
include "cmul.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvconst2.mm"
include "ad2antrl.mm"
include "fveq2d.mm"
include "nm0.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "cr.mm"
include "nmcl.mm"
include "ad2ant2r.mm"
include "recnd.mm"
include "mul02d.mm"
include "syl5breqr.mm"
include "eqbrtrd.mm"
include "nmolb2d.mm"
include "nmoge0.mm"
include "mpd3an3.mm"
include "cxr.mm"
include "wb.mm"
include "nmocl.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem nmo0
  let cS: class S
  let cT: class T
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let cF: class F
  let vx: setvar x
  assume nmo0.1: |- N = ( S normOp T )
  assume nmo0.2: |- V = ( Base ` S )
  assume nmo0.3: |- .0. = ( 0g ` T )


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp ) -> ( N ` ( V X. { .0. } ) ) = 0 )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    wa
    #
    cV
    c.0
    csn
    cxp
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @4
    cc0
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @2
    vx
    cc0
    cS
    cT
    @3
    cS
    cnm
    cfv
    #
    cT
    cnm
    cfv
    #
    cN
    cV
    cS
    c0g
    cfv
    #
    nmo0.1
    nmo0.2
    @8
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    @0
    @1
    simpl
    @0
    @1
    simpr
    @0
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    @3
    cS
    cT
    cghm
    co
    wcel
    #
    @1
    cS
    ngpgrp
    cT
    ngpgrp
    cV
    cS
    cT
    c.0
    nmo0.3
    nmo0.2
    0ghm
    syl2an
    #
    @2
    0red
    cc0
    cc0
    cle
    wbr
    @2
    0le0
    a1i
    @2
    vx
    cv
    #
    cV
    wcel
    #
    @15
    @10
    wne
    #
    wa
    #
    wa
    #
    @15
    @3
    cfv
    #
    @9
    cfv
    #
    cc0
    cc0
    @15
    @8
    cfv
    #
    cmul
    co
    #
    cle
    @19
    @21
    c.0
    @9
    cfv
    #
    cc0
    @19
    @20
    c.0
    @9
    @16
    @20
    c.0
    wceq
    @2
    @17
    cV
    c.0
    @15
    c.0
    cT
    c0g
    cfv
    cvv
    nmo0.3
    cT
    c0g
    fvex
    eqeltri
    fvconst2
    ad2antrl
    fveq2d
    @1
    @24
    cc0
    wceq
    @0
    @18
    cT
    @9
    c.0
    @12
    nmo0.3
    nm0
    ad2antlr
    eqtrd
    @19
    cc0
    cc0
    @23
    cle
    0le0
    @19
    @22
    @19
    @22
    @0
    @16
    @22
    cr
    wcel
    @1
    @17
    @15
    cS
    @8
    cV
    nmo0.2
    @11
    nmcl
    ad2ant2r
    recnd
    mul02d
    syl5breqr
    eqbrtrd
    nmolb2d
    @0
    @1
    @13
    @7
    @14
    cS
    cT
    @3
    cN
    nmo0.1
    nmoge0
    mpd3an3
    @2
    @4
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    @5
    @6
    @7
    wa
    wb
    @0
    @1
    @13
    @25
    @14
    cS
    cT
    @3
    cN
    nmo0.1
    nmocl
    mpd3an3
    0xr
    @4
    cc0
    xrletri3
    sylancl
    mpbir2and
end
