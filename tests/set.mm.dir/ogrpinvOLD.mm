include "cogrp.mm"
include "wcel.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "simplbi.mm"
include "grpidcl.mm"
include "syl.mm"
include "simp2.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "eqid.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "wceq.mm"
include "grplid.mm"
include "grprinv.mm"
include "3brtr3d.mm"

theorem ogrpinvOLD
  let cB: class B
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume ogrpsub.0: |- B = ( Base ` G )
  assume ogrpsub.1: |- .<_ = ( le ` G )
  assume ogrpinv.2: |- I = ( invg ` G )
  assume ogrpinv.3: |- .0. = ( 0g ` G )


  assert |- ( ( G e. oGrp /\ X e. B /\ .0. .<_ X ) -> ( I ` X ) .<_ .0. )

  proof
    cG
    cogrp
    wcel
    #
    cX
    cB
    wcel
    #
    c.0
    cX
    c.le
    wbr
    #
    w3a
    #
    c.0
    cX
    cI
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cX
    @4
    @5
    co
    #
    @4
    c.0
    c.le
    @3
    cG
    comnd
    wcel
    #
    c.0
    cB
    wcel
    #
    @1
    @4
    cB
    wcel
    #
    @2
    @6
    @7
    c.le
    wbr
    @0
    @1
    @8
    @2
    @0
    cG
    cgrp
    wcel
    #
    @8
    cG
    isogrp
    #
    simprbi
    3ad2ant1
    @3
    @11
    @9
    @0
    @1
    @11
    @2
    @0
    @11
    @8
    @12
    simplbi
    3ad2ant1
    #
    cB
    cG
    c.0
    ogrpsub.0
    ogrpinv.3
    grpidcl
    syl
    @0
    @1
    @2
    simp2
    #
    @3
    @11
    @1
    @10
    @13
    @14
    cB
    cG
    cI
    cX
    ogrpsub.0
    ogrpinv.2
    grpinvcl
    syl2anc
    #
    @0
    @1
    @2
    simp3
    cB
    @5
    c.le
    cG
    c.0
    cX
    @4
    ogrpsub.0
    ogrpsub.1
    @5
    eqid
    #
    omndadd
    syl131anc
    @3
    @11
    @10
    @6
    @4
    wceq
    @13
    @15
    cB
    @5
    cG
    @4
    c.0
    ogrpsub.0
    @16
    ogrpinv.3
    grplid
    syl2anc
    @3
    @11
    @1
    @7
    c.0
    wceq
    @13
    @14
    cB
    @5
    cG
    cI
    cX
    c.0
    ogrpsub.0
    @16
    ogrpinv.3
    ogrpinv.2
    grprinv
    syl2anc
    3brtr3d
end
