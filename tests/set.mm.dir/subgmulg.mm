include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "clt.mm"
include "wbr.mm"
include "cplusg.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cneg.mm"
include "cminusg.mm"
include "cif.mm"
include "co.mm"
include "eqid.mm"
include "subg0.mm"
include "3ad2ant1.mm"
include "ifeq1d.mm"
include "wn.mm"
include "wa.mm"
include "ressplusg.mm"
include "seqeq2d.mm"
include "adantr.mm"
include "fveq1d.mm"
include "wo.mm"
include "cr.mm"
include "wb.mm"
include "simp2.mm"
include "zred.mm"
include "0re.mm"
include "axlttri.mm"
include "sylancl.mm"
include "ioran.mm"
include "syl6bb.mm"
include "biimpar.mm"
include "simpl1.mm"
include "cbs.mm"
include "znegcld.mm"
include "lt0neg1d.mm"
include "biimpa.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "wss.mm"
include "subgss.mm"
include "simp3.mm"
include "sseldd.mm"
include "mulgnn.mm"
include "syl2anc.mm"
include "subgmulgcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "subginv.mm"
include "syldan.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "anassrs.mm"
include "ifeq2da.mm"
include "mulgval.mm"
include "subgbas.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"

theorem subgmulg
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume subgmulgcl.t: |- .x. = ( .g ` G )
  assume subgmulg.h: |- H = ( G |`s S )
  assume subgmulg.t: |- .xb = ( .g ` H )


  assert |- ( ( S e. ( SubGrp ` G ) /\ N e. ZZ /\ X e. S ) -> ( N .x. X ) = ( N .xb X ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cN
    cc0
    wceq
    #
    cG
    c0g
    cfv
    #
    cc0
    cN
    clt
    wbr
    #
    cN
    cG
    cplusg
    cfv
    #
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cN
    cneg
    #
    @10
    cfv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    cif
    #
    @5
    cH
    c0g
    cfv
    #
    @7
    cN
    cH
    cplusg
    cfv
    #
    @9
    c1
    cseq
    #
    cfv
    #
    @12
    @20
    cfv
    #
    cH
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    cif
    #
    cN
    cX
    c.x
    co
    #
    cN
    cX
    c.xb
    co
    #
    @4
    @17
    @5
    @18
    @16
    cif
    @26
    @4
    @5
    @6
    @18
    @16
    @1
    @2
    @6
    @18
    wceq
    @3
    cS
    cG
    cH
    @6
    subgmulg.h
    @6
    eqid
    #
    subg0
    3ad2ant1
    ifeq1d
    @4
    @5
    @16
    @25
    @18
    @4
    @5
    wn
    #
    wa
    #
    @16
    @7
    @21
    @15
    cif
    @25
    @31
    @7
    @11
    @21
    @15
    @31
    cN
    @10
    @20
    @4
    @10
    @20
    wceq
    #
    @30
    @4
    @8
    @19
    @9
    c1
    @1
    @2
    @8
    @19
    wceq
    @3
    cS
    @8
    cG
    cH
    @0
    subgmulg.h
    @8
    eqid
    #
    ressplusg
    3ad2ant1
    seqeq2d
    #
    adantr
    fveq1d
    ifeq1d
    @31
    @7
    @15
    @24
    @21
    @4
    @30
    @7
    wn
    #
    @15
    @24
    wceq
    @4
    @30
    @35
    wa
    #
    wa
    #
    @15
    @13
    @23
    cfv
    #
    @24
    @4
    @36
    cN
    cc0
    clt
    wbr
    #
    @15
    @38
    wceq
    #
    @4
    @39
    @36
    @4
    @39
    @5
    @7
    wo
    wn
    #
    @36
    @4
    cN
    cr
    wcel
    cc0
    cr
    wcel
    @39
    @41
    wb
    @4
    cN
    @1
    @2
    @3
    simp2
    #
    zred
    #
    0re
    cN
    cc0
    axlttri
    sylancl
    @5
    @7
    ioran
    syl6bb
    biimpar
    @4
    @39
    wa
    #
    @1
    @13
    cS
    wcel
    @40
    @1
    @2
    @3
    @39
    simpl1
    #
    @44
    @12
    cX
    c.x
    co
    #
    @13
    cS
    @44
    @12
    cn
    wcel
    #
    cX
    cG
    cbs
    cfv
    #
    wcel
    #
    @46
    @13
    wceq
    @44
    @12
    cz
    wcel
    #
    cc0
    @12
    clt
    wbr
    #
    @47
    @44
    cN
    @4
    @2
    @39
    @42
    adantr
    znegcld
    #
    @4
    @39
    @51
    @4
    cN
    @43
    lt0neg1d
    biimpa
    @12
    elnnz
    sylanbrc
    @4
    @49
    @39
    @4
    cS
    @48
    cX
    @1
    @2
    cS
    @48
    wss
    @3
    @48
    cS
    cG
    @48
    eqid
    #
    subgss
    3ad2ant1
    @1
    @2
    @3
    simp3
    #
    sseldd
    #
    adantr
    @48
    @8
    @10
    c.x
    cG
    @12
    cX
    @53
    @33
    subgmulgcl.t
    @10
    eqid
    #
    mulgnn
    syl2anc
    @44
    @1
    @50
    @3
    @46
    cS
    wcel
    @45
    @52
    @4
    @3
    @39
    @54
    adantr
    cS
    c.x
    cG
    @12
    cX
    subgmulgcl.t
    subgmulgcl
    syl3anc
    eqeltrrd
    cS
    cG
    cH
    @14
    @23
    @13
    subgmulg.h
    @14
    eqid
    #
    @23
    eqid
    #
    subginv
    syl2anc
    syldan
    @37
    @13
    @22
    @23
    @37
    @12
    @10
    @20
    @4
    @32
    @36
    @34
    adantr
    fveq1d
    fveq2d
    eqtrd
    anassrs
    ifeq2da
    eqtrd
    ifeq2da
    eqtrd
    @4
    @2
    @49
    @27
    @17
    wceq
    @42
    @55
    @48
    @8
    @10
    c.x
    cG
    @14
    cN
    cX
    @6
    @53
    @33
    @29
    @57
    subgmulgcl.t
    @56
    mulgval
    syl2anc
    @4
    @2
    cX
    cH
    cbs
    cfv
    #
    wcel
    @28
    @26
    wceq
    @42
    @4
    cX
    cS
    @59
    @54
    @1
    @2
    cS
    @59
    wceq
    @3
    cS
    cG
    cH
    subgmulg.h
    subgbas
    3ad2ant1
    eleqtrd
    @59
    @19
    @20
    c.xb
    cH
    @23
    cN
    cX
    @18
    @59
    eqid
    @19
    eqid
    @18
    eqid
    @58
    subgmulg.t
    @20
    eqid
    mulgval
    syl2anc
    3eqtr4d
end
