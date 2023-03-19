include "crn.mm"
include "cuni.mm"
include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "cdprd.mm"
include "co.mm"
include "cbs.mm"
include "cmre.mm"
include "wcel.mm"
include "wss.mm"
include "cgrp.mm"
include "cacs.mm"
include "subggrp.mm"
include "syl.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "subgrcl.mm"
include "cpw.mm"
include "cdm.mm"
include "wbr.mm"
include "wf.mm"
include "dprdf.mm"
include "frn.mm"
include "mresspw.mm"
include "sstrd.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrcssidd.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "wa.mm"
include "wb.mm"
include "subsubg.mm"
include "mpbir2and.mm"
include "subgdmdprd.mm"
include "eqidd.mm"
include "dprdf2.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqssd.mm"
include "wceq.mm"
include "dprdspan.mm"
include "3eqtr4d.mm"

theorem subgdprd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgdprd.1: |- H = ( G |`s A )
  assume subgdprd.2: |- ( ph -> A e. ( SubGrp ` G ) )
  assume subgdprd.3: |- ( ph -> G dom DProd S )
  assume subgdprd.4: |- ( ph -> ran S C_ ~P A )


  assert |- ( ph -> ( H DProd S ) = ( G DProd S ) )

  proof
    wph
    cS
    crn
    #
    cuni
    #
    cH
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    @1
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    cH
    cS
    cdprd
    co
    #
    cG
    cS
    cdprd
    co
    #
    wph
    @4
    @7
    wph
    @2
    cH
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    @1
    @7
    wss
    @7
    @2
    wcel
    #
    @4
    @7
    wss
    wph
    cH
    cgrp
    wcel
    #
    @2
    @10
    cacs
    cfv
    wcel
    @11
    wph
    cA
    @5
    wcel
    #
    @13
    subgdprd.2
    cA
    cG
    cH
    subgdprd.1
    subggrp
    syl
    @10
    cH
    @10
    eqid
    subgacs
    @2
    @10
    acsmre
    3syl
    #
    wph
    @5
    @1
    @6
    cG
    cbs
    cfv
    #
    wph
    cG
    cgrp
    wcel
    #
    @5
    @16
    cacs
    cfv
    wcel
    @5
    @16
    cmre
    cfv
    wcel
    #
    wph
    @14
    @17
    subgdprd.2
    cA
    cG
    subgrcl
    syl
    @16
    cG
    @16
    eqid
    subgacs
    @5
    @16
    acsmre
    3syl
    #
    @6
    eqid
    #
    wph
    @0
    @16
    cpw
    #
    wss
    @1
    @16
    wss
    #
    wph
    @0
    @5
    @21
    wph
    cG
    cS
    cdprd
    cdm
    #
    wbr
    #
    cS
    cdm
    #
    @5
    cS
    wf
    @0
    @5
    wss
    subgdprd.3
    cS
    cG
    dprdf
    @25
    @5
    cS
    frn
    3syl
    wph
    @18
    @5
    @21
    wss
    @19
    @5
    @16
    mresspw
    syl
    sstrd
    @0
    @16
    sspwuni
    sylib
    #
    mrcssidd
    wph
    @12
    @7
    @5
    wcel
    #
    @7
    cA
    wss
    #
    wph
    @18
    @22
    @27
    @19
    @26
    @5
    @1
    @6
    @16
    @20
    mrccl
    syl2anc
    wph
    @18
    @1
    cA
    wss
    #
    @14
    @28
    @19
    wph
    @0
    cA
    cpw
    wss
    #
    @29
    subgdprd.4
    @0
    cA
    sspwuni
    sylib
    subgdprd.2
    @5
    @1
    @6
    cA
    @16
    @20
    mrcsscl
    syl3anc
    wph
    @14
    @12
    @27
    @28
    wa
    wb
    subgdprd.2
    @7
    cA
    cG
    cH
    subgdprd.1
    subsubg
    syl
    mpbir2and
    @2
    @1
    @3
    @7
    @10
    @3
    eqid
    #
    mrcsscl
    syl3anc
    wph
    @18
    @1
    @4
    wss
    @4
    @5
    wcel
    #
    @7
    @4
    wss
    @19
    wph
    @2
    @1
    @3
    @10
    @15
    @31
    wph
    @0
    @10
    cpw
    #
    wss
    @1
    @10
    wss
    #
    wph
    @0
    @2
    @33
    wph
    @25
    @2
    cS
    wf
    @0
    @2
    wss
    wph
    cS
    cH
    @25
    wph
    cH
    cS
    @23
    wbr
    #
    @24
    @30
    subgdprd.3
    subgdprd.4
    wph
    @14
    @35
    @24
    @30
    wa
    wb
    subgdprd.2
    cA
    cS
    cG
    cH
    subgdprd.1
    subgdmdprd
    syl
    mpbir2and
    #
    wph
    @25
    eqidd
    dprdf2
    @25
    @2
    cS
    frn
    syl
    wph
    @11
    @2
    @33
    wss
    @15
    @2
    @10
    mresspw
    syl
    sstrd
    @0
    @10
    sspwuni
    sylib
    #
    mrcssidd
    wph
    @32
    @4
    cA
    wss
    #
    wph
    @4
    @2
    wcel
    #
    @32
    @38
    wa
    #
    wph
    @11
    @34
    @39
    @15
    @37
    @2
    @1
    @3
    @10
    @31
    mrccl
    syl2anc
    wph
    @14
    @39
    @40
    wb
    subgdprd.2
    @4
    cA
    cG
    cH
    subgdprd.1
    subsubg
    syl
    mpbid
    simpld
    @5
    @1
    @6
    @4
    @16
    @20
    mrcsscl
    syl3anc
    eqssd
    wph
    @35
    @8
    @4
    wceq
    @36
    cS
    cH
    @3
    @31
    dprdspan
    syl
    wph
    @24
    @9
    @7
    wceq
    subgdprd.3
    cS
    cG
    @6
    @20
    dprdspan
    syl
    3eqtr4d
end
