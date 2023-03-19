include "cogrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "ogrpaddlt.mm"
include "3expa.mm"
include "cminusg.mm"
include "cfv.mm"
include "simpll.mm"
include "cgrp.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "simplr1.mm"
include "simplr3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simplr2.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "syl131anc.mm"
include "c0g.mm"
include "wceq.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grprinv.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3eqtrd.mm"
include "3brtr3d.mm"
include "impbida.mm"

theorem ogrpaddltbi
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


  assert |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( X .< Y <-> ( X .+ Z ) .< ( Y .+ Z ) ) )

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
    wa
    #
    cX
    cY
    c.lt
    wbr
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
    @0
    @4
    @6
    @9
    cB
    c.pl
    c.lt
    cG
    cX
    cY
    cZ
    ogrpaddlt.0
    ogrpaddlt.1
    ogrpaddlt.2
    ogrpaddlt
    3expa
    @5
    @9
    wa
    #
    @7
    cZ
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    @8
    @12
    c.pl
    co
    #
    cX
    cY
    c.lt
    @10
    @0
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @9
    @13
    @14
    c.lt
    wbr
    @0
    @4
    @9
    simpll
    #
    @10
    cG
    cgrp
    wcel
    #
    @1
    @3
    @15
    @10
    @0
    @19
    @18
    cG
    ogrpgrp
    syl
    #
    @1
    @2
    @3
    @0
    @9
    simplr1
    #
    @1
    @2
    @3
    @0
    @9
    simplr3
    #
    cB
    c.pl
    cG
    cX
    cZ
    ogrpaddlt.0
    ogrpaddlt.2
    grpcl
    syl3anc
    @10
    @19
    @2
    @3
    @16
    @20
    @1
    @2
    @3
    @0
    @9
    simplr2
    #
    @22
    cB
    c.pl
    cG
    cY
    cZ
    ogrpaddlt.0
    ogrpaddlt.2
    grpcl
    syl3anc
    @10
    @19
    @3
    @17
    @20
    @22
    cB
    cG
    @11
    cZ
    ogrpaddlt.0
    @11
    eqid
    #
    grpinvcl
    syl2anc
    #
    @5
    @9
    simpr
    cB
    c.pl
    c.lt
    cG
    @7
    @8
    @12
    ogrpaddlt.0
    ogrpaddlt.1
    ogrpaddlt.2
    ogrpaddlt
    syl131anc
    @10
    @13
    cX
    cZ
    @12
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cG
    c0g
    cfv
    #
    c.pl
    co
    #
    cX
    @10
    @19
    @1
    @3
    @17
    @13
    @27
    wceq
    @20
    @21
    @22
    @25
    cB
    c.pl
    cG
    cX
    cZ
    @12
    ogrpaddlt.0
    ogrpaddlt.2
    grpass
    syl13anc
    @10
    @26
    @28
    cX
    c.pl
    @10
    @19
    @3
    @26
    @28
    wceq
    @20
    @22
    cB
    c.pl
    cG
    @11
    cZ
    @28
    ogrpaddlt.0
    ogrpaddlt.2
    @28
    eqid
    #
    @24
    grprinv
    syl2anc
    #
    oveq2d
    @10
    @19
    @1
    @29
    cX
    wceq
    @20
    @21
    cB
    c.pl
    cG
    cX
    @28
    ogrpaddlt.0
    ogrpaddlt.2
    @30
    grprid
    syl2anc
    3eqtrd
    @10
    @14
    cY
    @26
    c.pl
    co
    #
    cY
    @28
    c.pl
    co
    #
    cY
    @10
    @19
    @2
    @3
    @17
    @14
    @32
    wceq
    @20
    @23
    @22
    @25
    cB
    c.pl
    cG
    cY
    cZ
    @12
    ogrpaddlt.0
    ogrpaddlt.2
    grpass
    syl13anc
    @10
    @26
    @28
    cY
    c.pl
    @31
    oveq2d
    @10
    @19
    @2
    @33
    cY
    wceq
    @20
    @23
    cB
    c.pl
    cG
    cY
    @28
    ogrpaddlt.0
    ogrpaddlt.2
    @30
    grprid
    syl2anc
    3eqtrd
    3brtr3d
    impbida
end
