include "cogrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "simp3.mm"
include "wb.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "eqid.mm"
include "pltval.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "ogrpsub.mm"
include "syld3an3.mm"
include "simprd.mm"
include "cgrp.mm"
include "wceq.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "simp23.mm"
include "grpsubrcan.mm"
include "syl13anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "grpsubcl.mm"
include "mpbir2and.mm"

theorem ogrpsublt
  let cB: class B
  let c.lt: class .<
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ogrpsublt.0: |- B = ( Base ` G )
  assume ogrpsublt.1: |- .< = ( lt ` G )
  assume ogrpsublt.2: |- .- = ( -g ` G )


  assert |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X .< Y ) -> ( X .- Z ) .< ( Y .- Z ) )

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
    c.mi
    co
    #
    cY
    cZ
    c.mi
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
    @0
    @4
    @5
    cX
    cY
    @10
    wbr
    #
    @11
    @6
    @13
    cX
    cY
    wne
    #
    @6
    @5
    @13
    @14
    wa
    #
    @0
    @4
    @5
    simp3
    @6
    @0
    @1
    @2
    @5
    @15
    wb
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
    ogrpsublt.1
    pltval
    syl3anc
    mpbid
    #
    simpld
    cB
    cG
    @10
    c.mi
    cX
    cY
    cZ
    ogrpsublt.0
    @19
    ogrpsublt.2
    ogrpsub
    syld3an3
    @6
    @12
    @14
    @6
    @13
    @14
    @20
    simprd
    @6
    @7
    @8
    cX
    cY
    @6
    cG
    cgrp
    wcel
    #
    @1
    @2
    @3
    @7
    @8
    wceq
    cX
    cY
    wceq
    wb
    @6
    @0
    @21
    @16
    cG
    ogrpgrp
    syl
    #
    @17
    @18
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    cB
    cG
    c.mi
    cX
    cY
    cZ
    ogrpsublt.0
    ogrpsublt.2
    grpsubrcan
    syl13anc
    necon3bid
    mpbird
    @6
    @0
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @9
    @11
    @12
    wa
    wb
    @16
    @6
    @21
    @1
    @3
    @24
    @22
    @17
    @23
    cB
    cG
    c.mi
    cX
    cZ
    ogrpsublt.0
    ogrpsublt.2
    grpsubcl
    syl3anc
    @6
    @21
    @2
    @3
    @25
    @22
    @18
    @23
    cB
    cG
    c.mi
    cY
    cZ
    ogrpsublt.0
    ogrpsublt.2
    grpsubcl
    syl3anc
    cogrp
    cB
    cB
    c.lt
    cG
    @10
    @7
    @8
    @19
    ogrpsublt.1
    pltval
    syl3anc
    mpbir2and
end
