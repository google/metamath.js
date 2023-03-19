include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "csg.mm"
include "cfv.mm"
include "simpll.mm"
include "w3a.mm"
include "csubg.mm"
include "wer.mm"
include "clidl.mm"
include "coppr.mm"
include "eqid.mm"
include "2idlval.mm"
include "elin2.mm"
include "simplbi.mm"
include "ad2antlr.mm"
include "lidlsubg.mm"
include "syl2anc.mm"
include "eqger.mm"
include "syl.mm"
include "simprl.mm"
include "ersym.mm"
include "cabl.mm"
include "wss.mm"
include "wb.mm"
include "ringabl.mm"
include "ad2antrr.mm"
include "lidlss.mm"
include "eqgabl.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simprr.mm"
include "simp1d.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cgrp.mm"
include "wceq.mm"
include "ringgrp.mm"
include "grpnnncan2.mm"
include "syl13anc.mm"
include "ringsubdi.mm"
include "simp3d.mm"
include "lidlmcl.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "cmulr.mm"
include "opprmul.mm"
include "rngsubdir.mm"
include "syl5eq.mm"
include "opprring.mm"
include "simprbi.mm"
include "opprbas.mm"
include "lidlsubcl.mm"
include "mpbir3and.mm"
include "ex.mm"

theorem 2idlcpbl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cE: class E
  let cI: class I
  let cX: class X
  assume 2idlcpbl.x: |- X = ( Base ` R )
  assume 2idlcpbl.r: |- E = ( R ~QG S )
  assume 2idlcpbl.i: |- I = ( 2Ideal ` R )
  assume 2idlcpbl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ S e. I ) -> ( ( A E C /\ B E D ) -> ( A .x. B ) E ( C .x. D ) ) )

  proof
    cR
    crg
    wcel
    #
    cS
    cI
    wcel
    #
    wa
    #
    cA
    cC
    cE
    wbr
    #
    cB
    cD
    cE
    wbr
    #
    wa
    #
    cA
    cB
    c.x
    co
    #
    cC
    cD
    c.x
    co
    #
    cE
    wbr
    #
    @2
    @5
    wa
    #
    @8
    @6
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    @7
    @6
    cR
    csg
    cfv
    #
    co
    #
    cS
    wcel
    #
    @9
    @0
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @10
    @0
    @1
    @5
    simpll
    #
    @9
    cC
    cX
    wcel
    #
    @15
    cA
    cC
    @12
    co
    #
    cS
    wcel
    #
    @9
    cC
    cA
    cE
    wbr
    #
    @18
    @15
    @20
    w3a
    #
    @9
    cA
    cC
    cE
    cX
    @9
    cS
    cR
    csubg
    cfv
    wcel
    #
    cX
    cE
    wer
    @9
    @0
    cS
    cR
    clidl
    cfv
    #
    wcel
    #
    @23
    @17
    @1
    @25
    @0
    @5
    @1
    @25
    cS
    cR
    coppr
    cfv
    #
    clidl
    cfv
    #
    wcel
    #
    cS
    @24
    @27
    cI
    cR
    cI
    @24
    @27
    @26
    @24
    eqid
    #
    @26
    eqid
    #
    @27
    eqid
    #
    2idlcpbl.i
    2idlval
    elin2
    #
    simplbi
    ad2antlr
    #
    cR
    @24
    cS
    @29
    lidlsubg
    syl2anc
    cE
    cR
    cX
    cS
    2idlcpbl.x
    2idlcpbl.r
    eqger
    syl
    @2
    @3
    @4
    simprl
    ersym
    @9
    cR
    cabl
    wcel
    #
    cS
    cX
    wss
    #
    @21
    @22
    wb
    @0
    @34
    @1
    @5
    cR
    ringabl
    ad2antrr
    #
    @9
    @25
    @35
    @33
    cX
    cS
    @24
    cR
    2idlcpbl.x
    @29
    lidlss
    syl
    #
    cC
    cA
    cE
    cS
    cR
    @12
    cX
    2idlcpbl.x
    @12
    eqid
    #
    2idlcpbl.r
    eqgabl
    syl2anc
    mpbid
    #
    simp2d
    #
    @9
    @16
    cD
    cX
    wcel
    #
    cD
    cB
    @12
    co
    #
    cS
    wcel
    #
    @9
    @4
    @16
    @41
    @43
    w3a
    #
    @2
    @3
    @4
    simprr
    @9
    @34
    @35
    @4
    @44
    wb
    @36
    @37
    cB
    cD
    cE
    cS
    cR
    @12
    cX
    2idlcpbl.x
    @38
    2idlcpbl.r
    eqgabl
    syl2anc
    mpbid
    #
    simp1d
    #
    cX
    cR
    c.x
    cA
    cB
    2idlcpbl.x
    2idlcpbl.t
    ringcl
    syl3anc
    #
    @9
    @0
    @18
    @41
    @11
    @17
    @9
    @18
    @15
    @20
    @39
    simp1d
    #
    @9
    @16
    @41
    @43
    @45
    simp2d
    #
    cX
    cR
    c.x
    cC
    cD
    2idlcpbl.x
    2idlcpbl.t
    ringcl
    syl3anc
    #
    @9
    @7
    cC
    cB
    c.x
    co
    #
    @12
    co
    #
    @6
    @51
    @12
    co
    #
    @12
    co
    #
    @13
    cS
    @9
    cR
    cgrp
    wcel
    #
    @11
    @10
    @51
    cX
    wcel
    #
    @54
    @13
    wceq
    @0
    @55
    @1
    @5
    cR
    ringgrp
    ad2antrr
    @50
    @47
    @9
    @0
    @18
    @16
    @56
    @17
    @48
    @46
    cX
    cR
    c.x
    cC
    cB
    2idlcpbl.x
    2idlcpbl.t
    ringcl
    syl3anc
    cX
    cR
    @12
    @7
    @6
    @51
    2idlcpbl.x
    @38
    grpnnncan2
    syl13anc
    @9
    @0
    @25
    @52
    cS
    wcel
    @53
    cS
    wcel
    @54
    cS
    wcel
    @17
    @33
    @9
    cC
    @42
    c.x
    co
    #
    @52
    cS
    @9
    cX
    cR
    c.x
    @12
    cC
    cD
    cB
    2idlcpbl.x
    2idlcpbl.t
    @38
    @17
    @48
    @49
    @46
    ringsubdi
    @9
    @0
    @25
    @18
    @43
    @57
    cS
    wcel
    @17
    @33
    @48
    @9
    @16
    @41
    @43
    @45
    simp3d
    cX
    cR
    c.x
    @24
    cS
    cC
    @42
    @29
    2idlcpbl.x
    2idlcpbl.t
    lidlmcl
    syl22anc
    eqeltrrd
    @9
    cB
    @19
    @26
    cmulr
    cfv
    #
    co
    #
    @53
    cS
    @9
    @59
    @19
    cB
    c.x
    co
    @53
    cX
    cR
    @58
    c.x
    @26
    cB
    @19
    2idlcpbl.x
    2idlcpbl.t
    @30
    @58
    eqid
    #
    opprmul
    @9
    cX
    cR
    c.x
    @12
    cA
    cC
    cB
    2idlcpbl.x
    2idlcpbl.t
    @38
    @17
    @40
    @48
    @46
    rngsubdir
    syl5eq
    @9
    @26
    crg
    wcel
    #
    @28
    @16
    @20
    @59
    cS
    wcel
    @0
    @61
    @1
    @5
    cR
    @26
    @30
    opprring
    ad2antrr
    @1
    @28
    @0
    @5
    @1
    @25
    @28
    @32
    simprbi
    ad2antlr
    @46
    @9
    @18
    @15
    @20
    @39
    simp3d
    cX
    @26
    @58
    @27
    cS
    cB
    @19
    @31
    cX
    cR
    @26
    @30
    2idlcpbl.x
    opprbas
    @60
    lidlmcl
    syl22anc
    eqeltrrd
    cR
    @24
    cS
    @12
    @52
    @53
    @29
    @38
    lidlsubcl
    syl22anc
    eqeltrrd
    @9
    @34
    @35
    @8
    @10
    @11
    @14
    w3a
    wb
    @36
    @37
    @6
    @7
    cE
    cS
    cR
    @12
    cX
    2idlcpbl.x
    @38
    2idlcpbl.r
    eqgabl
    syl2anc
    mpbir3and
    ex
end
