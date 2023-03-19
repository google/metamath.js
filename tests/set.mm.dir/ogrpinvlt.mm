include "cogrp.mm"
include "wcel.mm"
include "coppg.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "wb.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3.mm"
include "cgrp.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ogrpaddltbi.mm"
include "syl13anc.mm"
include "wceq.mm"
include "grprinv.mm"
include "breq2d.mm"
include "simp1r.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "grpidcl.mm"
include "3syl.mm"
include "ogrpaddltrbid.mm"
include "3bitrd.mm"
include "grplinv.mm"
include "oveq1d.mm"
include "grpass.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "grprid.mm"
include "breq12d.mm"
include "bitrd.mm"

theorem ogrpinvlt
  let cB: class B
  let c.lt: class .<
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  assume ogrpinvlt.0: |- B = ( Base ` G )
  assume ogrpinvlt.1: |- .< = ( lt ` G )
  assume ogrpinvlt.2: |- I = ( invg ` G )


  assert |- ( ( ( G e. oGrp /\ ( oppG ` G ) e. oGrp ) /\ X e. B /\ Y e. B ) -> ( X .< Y <-> ( I ` Y ) .< ( I ` X ) ) )

  proof
    cG
    cogrp
    wcel
    #
    cG
    coppg
    cfv
    cogrp
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
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
    cX
    cI
    cfv
    #
    cX
    cY
    cI
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @9
    co
    #
    @7
    cG
    c0g
    cfv
    #
    @9
    co
    #
    c.lt
    wbr
    #
    @8
    @7
    c.lt
    wbr
    @5
    @6
    @10
    cY
    @8
    @9
    co
    #
    c.lt
    wbr
    #
    @10
    @12
    c.lt
    wbr
    @14
    @5
    @0
    @3
    @4
    @8
    cB
    wcel
    #
    @6
    @16
    wb
    @0
    @1
    @3
    @4
    simp1l
    #
    @2
    @3
    @4
    simp2
    #
    @2
    @3
    @4
    simp3
    #
    @5
    cG
    cgrp
    wcel
    #
    @4
    @17
    @5
    @0
    @21
    @18
    cG
    ogrpgrp
    #
    syl
    #
    @20
    cB
    cG
    cI
    cY
    ogrpinvlt.0
    ogrpinvlt.2
    grpinvcl
    syl2anc
    #
    cB
    @9
    c.lt
    cG
    cX
    cY
    @8
    ogrpinvlt.0
    ogrpinvlt.1
    @9
    eqid
    #
    ogrpaddltbi
    syl13anc
    @5
    @15
    @12
    @10
    c.lt
    @5
    @21
    @4
    @15
    @12
    wceq
    @23
    @20
    cB
    @9
    cG
    cI
    cY
    @12
    ogrpinvlt.0
    @25
    @12
    eqid
    #
    ogrpinvlt.2
    grprinv
    syl2anc
    breq2d
    @5
    cB
    @9
    c.lt
    cG
    cogrp
    @10
    @12
    @7
    ogrpinvlt.0
    ogrpinvlt.1
    @25
    @18
    @0
    @1
    @3
    @4
    simp1r
    @5
    @21
    @3
    @17
    @10
    cB
    wcel
    @23
    @19
    @24
    cB
    @9
    cG
    cX
    @8
    ogrpinvlt.0
    @25
    grpcl
    syl3anc
    @5
    @0
    @21
    @12
    cB
    wcel
    @18
    @22
    cB
    cG
    @12
    ogrpinvlt.0
    @26
    grpidcl
    3syl
    @5
    @21
    @3
    @7
    cB
    wcel
    #
    @23
    @19
    cB
    cG
    cI
    cX
    ogrpinvlt.0
    ogrpinvlt.2
    grpinvcl
    syl2anc
    #
    ogrpaddltrbid
    3bitrd
    @5
    @11
    @8
    @13
    @7
    c.lt
    @5
    @7
    cX
    @9
    co
    #
    @8
    @9
    co
    #
    @12
    @8
    @9
    co
    #
    @11
    @8
    @5
    @29
    @12
    @8
    @9
    @5
    @21
    @3
    @29
    @12
    wceq
    @23
    @19
    cB
    @9
    cG
    cI
    cX
    @12
    ogrpinvlt.0
    @25
    @26
    ogrpinvlt.2
    grplinv
    syl2anc
    oveq1d
    @5
    @21
    @27
    @3
    @17
    @30
    @11
    wceq
    @23
    @28
    @19
    @24
    cB
    @9
    cG
    @7
    cX
    @8
    ogrpinvlt.0
    @25
    grpass
    syl13anc
    @5
    @21
    @17
    @31
    @8
    wceq
    @23
    @24
    cB
    @9
    cG
    @8
    @12
    ogrpinvlt.0
    @25
    @26
    grplid
    syl2anc
    3eqtr3d
    @5
    @21
    @27
    @13
    @7
    wceq
    @23
    @28
    cB
    @9
    cG
    @7
    @12
    ogrpinvlt.0
    @25
    @26
    grprid
    syl2anc
    breq12d
    bitrd
end
