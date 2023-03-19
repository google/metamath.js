include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cgrp.mm"
include "ctmd.mm"
include "cminusg.mm"
include "ctopn.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "subggrp.mm"
include "adantl.mm"
include "csubmnd.mm"
include "tgptmd.mm"
include "subgsubm.mm"
include "submtmd.mm"
include "syl2an.mm"
include "cv.mm"
include "cmpt.mm"
include "cbs.mm"
include "wceq.mm"
include "subgbas.mm"
include "mpteq1d.mm"
include "eqid.mm"
include "subginv.mm"
include "adantll.mm"
include "mpteq2dva.mm"
include "wf.mm"
include "grpinvf.mm"
include "syl.mm"
include "feqmptd.mm"
include "3eqtr4rd.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "adantr.mm"
include "wss.mm"
include "subgss.mm"
include "tgpgrp.mm"
include "tgpinv.mm"
include "eqeltrrd.mm"
include "cnmpt1res.mm"
include "eqeltrd.mm"
include "crn.mm"
include "wb.mm"
include "frn.mm"
include "sseqtr4d.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "resstopn.mm"
include "istgp.mm"
include "syl3anbrc.mm"

theorem subgtgp
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgtgp.h: |- H = ( G |`s S )


  assert |- ( ( G e. TopGrp /\ S e. ( SubGrp ` G ) ) -> H e. TopGrp )

  proof
    cG
    ctgp
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    wa
    #
    cH
    cgrp
    wcel
    #
    cH
    ctmd
    wcel
    #
    cH
    cminusg
    cfv
    #
    cG
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @7
    ccn
    co
    wcel
    #
    cH
    ctgp
    wcel
    @1
    @3
    @0
    cS
    cG
    cH
    subgtgp.h
    subggrp
    adantl
    #
    @0
    cG
    ctmd
    wcel
    cS
    cG
    csubmnd
    cfv
    wcel
    @4
    @1
    cG
    tgptmd
    cS
    cG
    subgsubm
    cS
    cG
    cH
    subgtgp.h
    submtmd
    syl2an
    @2
    @5
    @7
    @6
    ccn
    co
    #
    wcel
    #
    @8
    @2
    @5
    vx
    cS
    vx
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cmpt
    #
    @10
    @2
    vx
    cS
    @12
    @5
    cfv
    #
    cmpt
    vx
    cH
    cbs
    cfv
    #
    @16
    cmpt
    @15
    @5
    @2
    vx
    cS
    @17
    @16
    @1
    cS
    @17
    wceq
    @0
    cS
    cG
    cH
    subgtgp.h
    subgbas
    adantl
    #
    mpteq1d
    @2
    vx
    cS
    @14
    @16
    @1
    @12
    cS
    wcel
    @14
    @16
    wceq
    @0
    cS
    cG
    cH
    @13
    @5
    @12
    subgtgp.h
    @13
    eqid
    #
    @5
    eqid
    #
    subginv
    adantll
    mpteq2dva
    @2
    vx
    @17
    @17
    @5
    @2
    @3
    @17
    @17
    @5
    wf
    #
    @9
    @17
    cH
    @5
    @17
    eqid
    @20
    grpinvf
    syl
    #
    feqmptd
    3eqtr4rd
    @2
    vx
    @14
    @6
    @7
    @6
    cG
    cbs
    cfv
    #
    cS
    @7
    eqid
    @0
    @6
    @23
    ctopon
    cfv
    wcel
    #
    @1
    cG
    @6
    @23
    @6
    eqid
    #
    @23
    eqid
    #
    tgptopon
    adantr
    #
    @1
    cS
    @23
    wss
    #
    @0
    @23
    cS
    cG
    @26
    subgss
    adantl
    #
    @2
    @13
    vx
    @23
    @14
    cmpt
    @6
    @6
    ccn
    co
    #
    @2
    vx
    @23
    @23
    @13
    @2
    cG
    cgrp
    wcel
    #
    @23
    @23
    @13
    wf
    @0
    @31
    @1
    cG
    tgpgrp
    adantr
    @23
    cG
    @13
    @26
    @19
    grpinvf
    syl
    feqmptd
    @0
    @13
    @30
    wcel
    @1
    cG
    @13
    @6
    @25
    @19
    tgpinv
    adantr
    eqeltrrd
    cnmpt1res
    eqeltrd
    @2
    @24
    @5
    crn
    #
    cS
    wss
    @28
    @11
    @8
    wb
    @27
    @2
    @32
    @17
    cS
    @2
    @21
    @32
    @17
    wss
    @22
    @17
    @17
    @5
    frn
    syl
    @18
    sseqtr4d
    @29
    cS
    @5
    @7
    @6
    @23
    cnrest2
    syl3anc
    mpbid
    cH
    @5
    @7
    cS
    cH
    @6
    cG
    subgtgp.h
    @25
    resstopn
    @20
    istgp
    syl3anbrc
end
