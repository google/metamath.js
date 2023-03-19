include "cogrp.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "ad2antrr.mm"
include "cmnd.mm"
include "omndmnd.mm"
include "mndidcl.mm"
include "3syl.mm"
include "simplr.mm"
include "ogrpgrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eqid.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "wceq.mm"
include "grplid.mm"
include "grprinv.mm"
include "3brtr3d.mm"
include "grplinv.mm"
include "impbida.mm"

theorem ogrpinv0le
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


  assert |- ( ( G e. oGrp /\ X e. B ) -> ( .0. .<_ X <-> ( I ` X ) .<_ .0. ) )

  proof
    cG
    cogrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.0
    cX
    c.le
    wbr
    #
    cX
    cI
    cfv
    #
    c.0
    c.le
    wbr
    #
    @2
    @3
    wa
    #
    c.0
    @4
    cG
    cplusg
    cfv
    #
    co
    #
    cX
    @4
    @7
    co
    #
    @4
    c.0
    c.le
    @6
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
    @3
    @8
    @9
    c.le
    wbr
    @0
    @10
    @1
    @3
    @0
    cG
    cgrp
    wcel
    #
    @10
    cG
    isogrp
    simprbi
    #
    ad2antrr
    #
    @6
    @10
    cG
    cmnd
    wcel
    #
    @11
    @15
    cG
    omndmnd
    #
    cB
    cG
    c.0
    ogrpsub.0
    ogrpinv.3
    mndidcl
    #
    3syl
    @0
    @1
    @3
    simplr
    #
    @6
    @13
    @1
    @12
    @0
    @13
    @1
    @3
    cG
    ogrpgrp
    #
    ad2antrr
    #
    @19
    cB
    cG
    cI
    cX
    ogrpsub.0
    ogrpinv.2
    grpinvcl
    #
    syl2anc
    #
    @2
    @3
    simpr
    cB
    @7
    c.le
    cG
    c.0
    cX
    @4
    ogrpsub.0
    ogrpsub.1
    @7
    eqid
    #
    omndadd
    syl131anc
    @6
    @13
    @12
    @8
    @4
    wceq
    @21
    @23
    cB
    @7
    cG
    @4
    c.0
    ogrpsub.0
    @24
    ogrpinv.3
    grplid
    syl2anc
    @6
    @13
    @1
    @9
    c.0
    wceq
    @21
    @19
    cB
    @7
    cG
    cI
    cX
    c.0
    ogrpsub.0
    @24
    ogrpinv.3
    ogrpinv.2
    grprinv
    syl2anc
    3brtr3d
    @2
    @5
    wa
    #
    @4
    cX
    @7
    co
    #
    c.0
    cX
    @7
    co
    #
    c.0
    cX
    c.le
    @25
    @10
    @12
    @11
    @1
    @5
    @26
    @27
    c.le
    wbr
    @0
    @10
    @1
    @5
    @14
    ad2antrr
    #
    @25
    @13
    @1
    @12
    @0
    @13
    @1
    @5
    @20
    ad2antrr
    #
    @0
    @1
    @5
    simplr
    #
    @22
    syl2anc
    @25
    @10
    @16
    @11
    @28
    @17
    @18
    3syl
    @30
    @2
    @5
    simpr
    cB
    @7
    c.le
    cG
    @4
    c.0
    cX
    ogrpsub.0
    ogrpsub.1
    @24
    omndadd
    syl131anc
    @25
    @13
    @1
    @26
    c.0
    wceq
    @29
    @30
    cB
    @7
    cG
    cI
    cX
    c.0
    ogrpsub.0
    @24
    ogrpinv.3
    ogrpinv.2
    grplinv
    syl2anc
    @25
    @13
    @1
    @27
    cX
    wceq
    @29
    @30
    cB
    @7
    cG
    cX
    c.0
    ogrpsub.0
    @24
    ogrpinv.3
    grplid
    syl2anc
    3brtr3d
    impbida
end
