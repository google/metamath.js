include "cgrp.mm"
include "wcel.mm"
include "csn.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "eqid.mm"
include "grpidcl.mm"
include "snssd.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snnz.mm"
include "a1i.mm"
include "wceq.mm"
include "grplid.mm"
include "mpdan.mm"
include "ovex.mm"
include "elsn.mm"
include "sylibr.mm"
include "grpinvid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "ralsn.mm"
include "syl6bb.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "sylanbrc.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem 0subg
  let cG: class G
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume 0subg.z: |- .0. = ( 0g ` G )


  assert |- ( G e. Grp -> { .0. } e. ( SubGrp ` G ) )

  proof
    cG
    cgrp
    wcel
    #
    c.0
    csn
    #
    cG
    csubg
    cfv
    wcel
    @1
    cG
    cbs
    cfv
    #
    wss
    @1
    c0
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @1
    wcel
    #
    vb
    @1
    wral
    #
    @4
    cG
    cminusg
    cfv
    #
    cfv
    #
    @1
    wcel
    #
    wa
    #
    va
    @1
    wral
    #
    @0
    c.0
    @2
    @2
    cG
    c.0
    @2
    eqid
    #
    0subg.z
    grpidcl
    #
    snssd
    @3
    @0
    c.0
    c.0
    cG
    c0g
    cfv
    cvv
    0subg.z
    cG
    c0g
    fvex
    eqeltri
    #
    snnz
    a1i
    @0
    c.0
    c.0
    @6
    co
    #
    @1
    wcel
    #
    c.0
    @10
    cfv
    #
    @1
    wcel
    #
    @14
    @0
    @18
    c.0
    wceq
    #
    @19
    @0
    c.0
    @2
    wcel
    @22
    @16
    @2
    @6
    cG
    c.0
    c.0
    @15
    @6
    eqid
    #
    0subg.z
    grplid
    mpdan
    @18
    c.0
    c.0
    c.0
    @6
    ovex
    elsn
    sylibr
    @0
    @20
    c.0
    wceq
    @21
    cG
    @10
    c.0
    0subg.z
    @10
    eqid
    #
    grpinvid
    @20
    c.0
    c.0
    @10
    fvex
    elsn
    sylibr
    @13
    @19
    @21
    wa
    va
    c.0
    @17
    @4
    c.0
    wceq
    #
    @9
    @19
    @12
    @21
    @25
    @9
    c.0
    @5
    @6
    co
    #
    @1
    wcel
    #
    vb
    @1
    wral
    @19
    @25
    @8
    @27
    vb
    @1
    @25
    @7
    @26
    @1
    @4
    c.0
    @5
    @6
    oveq1
    eleq1d
    ralbidv
    @27
    @19
    vb
    c.0
    @17
    @5
    c.0
    wceq
    @26
    @18
    @1
    @5
    c.0
    c.0
    @6
    oveq2
    eleq1d
    ralsn
    syl6bb
    @25
    @11
    @20
    @1
    @4
    c.0
    @10
    fveq2
    eleq1d
    anbi12d
    ralsn
    sylanbrc
    va
    vb
    @2
    @6
    @1
    cG
    @10
    @15
    @23
    @24
    issubg2
    mpbir3and
end
