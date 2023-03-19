include "cogrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp22.mm"
include "ogrpgrp.mm"
include "simp23.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "wceq.mm"
include "grpsubval.mm"
include "3brtr4d.mm"

theorem ogrpsub
  let cB: class B
  let cG: class G
  let c.le: class .<_
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ogrpsub.0: |- B = ( Base ` G )
  assume ogrpsub.1: |- .<_ = ( le ` G )
  assume ogrpsub.2: |- .- = ( -g ` G )


  assert |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X .<_ Y ) -> ( X .- Z ) .<_ ( Y .- Z ) )

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
    c.le
    wbr
    #
    w3a
    #
    cX
    cZ
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cY
    @8
    @9
    co
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
    c.le
    @6
    cG
    comnd
    wcel
    #
    @1
    @2
    @8
    cB
    wcel
    #
    @5
    @10
    @11
    c.le
    wbr
    @0
    @4
    @14
    @5
    @0
    cG
    cgrp
    wcel
    #
    @14
    cG
    isogrp
    simprbi
    3ad2ant1
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
    @6
    @16
    @3
    @15
    @0
    @4
    @16
    @5
    cG
    ogrpgrp
    3ad2ant1
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    cB
    cG
    @7
    cZ
    ogrpsub.0
    @7
    eqid
    #
    grpinvcl
    syl2anc
    @0
    @4
    @5
    simp3
    cB
    @9
    c.le
    cG
    cX
    cY
    @8
    ogrpsub.0
    ogrpsub.1
    @9
    eqid
    #
    omndadd
    syl131anc
    @6
    @1
    @3
    @12
    @10
    wceq
    @17
    @19
    cB
    @9
    cG
    @7
    c.mi
    cX
    cZ
    ogrpsub.0
    @21
    @20
    ogrpsub.2
    grpsubval
    syl2anc
    @6
    @2
    @3
    @13
    @11
    wceq
    @18
    @19
    cB
    @9
    cG
    @7
    c.mi
    cY
    cZ
    ogrpsub.0
    @21
    @20
    ogrpsub.2
    grpsubval
    syl2anc
    3brtr4d
end
