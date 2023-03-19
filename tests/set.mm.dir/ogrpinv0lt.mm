include "cogrp.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "simpll.mm"
include "cgrp.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "grpidcl.mm"
include "simplr.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eqid.mm"
include "ogrpaddlt.mm"
include "syl131anc.mm"
include "wceq.mm"
include "grplid.mm"
include "grprinv.mm"
include "3brtr3d.mm"
include "3syl.mm"
include "grplinv.mm"
include "impbida.mm"

theorem ogrpinv0lt
  let cB: class B
  let c.lt: class .<
  let cG: class G
  let cI: class I
  let cX: class X
  let c.0: class .0.
  assume ogrpinvlt.0: |- B = ( Base ` G )
  assume ogrpinvlt.1: |- .< = ( lt ` G )
  assume ogrpinvlt.2: |- I = ( invg ` G )
  assume ogrpinv0lt.3: |- .0. = ( 0g ` G )


  assert |- ( ( G e. oGrp /\ X e. B ) -> ( .0. .< X <-> ( I ` X ) .< .0. ) )

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
    c.lt
    wbr
    #
    cX
    cI
    cfv
    #
    c.0
    c.lt
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
    c.lt
    @6
    @0
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
    c.lt
    wbr
    @0
    @1
    @3
    simpll
    #
    @6
    cG
    cgrp
    wcel
    #
    @10
    @6
    @0
    @13
    @12
    cG
    ogrpgrp
    #
    syl
    #
    cB
    cG
    c.0
    ogrpinvlt.0
    ogrpinv0lt.3
    grpidcl
    #
    syl
    @0
    @1
    @3
    simplr
    #
    @6
    @13
    @1
    @11
    @15
    @17
    cB
    cG
    cI
    cX
    ogrpinvlt.0
    ogrpinvlt.2
    grpinvcl
    #
    syl2anc
    #
    @2
    @3
    simpr
    cB
    @7
    c.lt
    cG
    c.0
    cX
    @4
    ogrpinvlt.0
    ogrpinvlt.1
    @7
    eqid
    #
    ogrpaddlt
    syl131anc
    @6
    @13
    @11
    @8
    @4
    wceq
    @15
    @19
    cB
    @7
    cG
    @4
    c.0
    ogrpinvlt.0
    @20
    ogrpinv0lt.3
    grplid
    syl2anc
    @6
    @13
    @1
    @9
    c.0
    wceq
    @15
    @17
    cB
    @7
    cG
    cI
    cX
    c.0
    ogrpinvlt.0
    @20
    ogrpinv0lt.3
    ogrpinvlt.2
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
    c.lt
    @21
    @0
    @11
    @10
    @1
    @5
    @22
    @23
    c.lt
    wbr
    @0
    @1
    @5
    simpll
    #
    @21
    @13
    @1
    @11
    @21
    @0
    @13
    @24
    @14
    syl
    #
    @0
    @1
    @5
    simplr
    #
    @18
    syl2anc
    @21
    @0
    @13
    @10
    @24
    @14
    @16
    3syl
    @26
    @2
    @5
    simpr
    cB
    @7
    c.lt
    cG
    @4
    c.0
    cX
    ogrpinvlt.0
    ogrpinvlt.1
    @20
    ogrpaddlt
    syl131anc
    @21
    @13
    @1
    @22
    c.0
    wceq
    @25
    @26
    cB
    @7
    cG
    cI
    cX
    c.0
    ogrpinvlt.0
    @20
    ogrpinv0lt.3
    ogrpinvlt.2
    grplinv
    syl2anc
    @21
    @13
    @1
    @23
    cX
    wceq
    @25
    @26
    cB
    @7
    cG
    cX
    c.0
    ogrpinvlt.0
    @20
    ogrpinv0lt.3
    grplid
    syl2anc
    3brtr3d
    impbida
end
