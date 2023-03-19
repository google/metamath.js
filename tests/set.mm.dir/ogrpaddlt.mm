include "cogrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3.mm"
include "eqid.mm"
include "pltle.mm"
include "imp.mm"
include "syl31anc.mm"
include "omndadd.mm"
include "syl3anc.mm"
include "pltne.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "ogrpgrp.mm"
include "grprcan.mm"
include "biimpd.mm"
include "sylan.mm"
include "necon3d.mm"
include "3impia.mm"
include "wb.mm"
include "cvv.mm"
include "ovex.mm"
include "pltval.mm"
include "mp3an23.mm"
include "mpbir2and.mm"

theorem ogrpaddlt
  let cB: class B
  let c.pl: class .+
  let c.lt: class .<
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ogrpaddlt.0: |- B = ( Base ` G )
  assume ogrpaddlt.1: |- .< = ( lt ` G )
  assume ogrpaddlt.2: |- .+ = ( +g ` G )


  assert |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X .< Y ) -> ( X .+ Z ) .< ( Y .+ Z ) )

  proof
    cG
    cogrp
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    w3a
    #
    cX
    cZ
    c.pl
    co
    #
    cY
    cZ
    c.pl
    co
    #
    c.lt
    wbr
    #
    @7
    @8
    cG
    cple
    cfv
    #
    wbr
    #
    @7
    @8
    wne
    #
    @6
    cG
    comnd
    wcel
    #
    @4
    cX
    cY
    @10
    wbr
    #
    @11
    @0
    @4
    @13
    @5
    @0
    cG
    cgrp
    wcel
    #
    @13
    cG
    isogrp
    simprbi
    3ad2ant1
    @0
    @4
    @5
    simp2
    #
    @6
    @0
    @1
    @2
    @5
    @14
    @0
    @4
    @5
    simp1
    #
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    @0
    @4
    @5
    simp3
    #
    @0
    @1
    @2
    w3a
    #
    @5
    @14
    cogrp
    cB
    cB
    c.lt
    cG
    @10
    cX
    cY
    @10
    eqid
    #
    ogrpaddlt.1
    pltle
    imp
    syl31anc
    cB
    c.pl
    @10
    cG
    cX
    cY
    cZ
    ogrpaddlt.0
    @22
    ogrpaddlt.2
    omndadd
    syl3anc
    @6
    @0
    @4
    cX
    cY
    wne
    #
    @12
    @17
    @16
    @6
    @0
    @1
    @2
    @5
    @23
    @17
    @18
    @19
    @20
    @21
    @5
    @23
    cogrp
    cB
    cB
    c.lt
    cG
    cX
    cY
    ogrpaddlt.1
    pltne
    imp
    syl31anc
    @0
    @4
    @23
    @12
    @0
    @4
    wa
    @7
    @8
    cX
    cY
    @0
    @15
    @4
    @7
    @8
    wceq
    #
    cX
    cY
    wceq
    #
    wi
    cG
    ogrpgrp
    @15
    @4
    wa
    @24
    @25
    cB
    c.pl
    cG
    cX
    cY
    cZ
    ogrpaddlt.0
    ogrpaddlt.2
    grprcan
    biimpd
    sylan
    necon3d
    3impia
    syl3anc
    @0
    @4
    @9
    @11
    @12
    wa
    wb
    #
    @5
    @0
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @26
    cX
    cZ
    c.pl
    ovex
    cY
    cZ
    c.pl
    ovex
    cogrp
    cvv
    cvv
    c.lt
    cG
    @10
    @7
    @8
    @22
    ogrpaddlt.1
    pltval
    mp3an23
    3ad2ant1
    mpbir2and
end
