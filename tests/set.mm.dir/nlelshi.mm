include "cnl.mm"
include "cfv.mm"
include "csh.mm"
include "wcel.mm"
include "c0v.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "wa.mm"
include "chil.mm"
include "cc0.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "lnfn0i.mm"
include "wf.mm"
include "wb.mm"
include "lnfnfi.mm"
include "elnlfn.mm"
include "ax-mp.mm"
include "mpbir2an.mm"
include "cdm.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "nlfnval.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "sseli.mm"
include "hvaddcl.mm"
include "syl2an.mm"
include "caddc.mm"
include "lnfnaddi.mm"
include "simprbi.mm"
include "oveqan12d.mm"
include "eqtrd.mm"
include "00id.mm"
include "syl6eq.mm"
include "sylanbrc.mm"
include "rgen2.mm"
include "hvmulcl.mm"
include "sylan2.mm"
include "cmul.mm"
include "lnfnmuli.mm"
include "oveq2d.mm"
include "mul01.mm"
include "sylan9eqr.mm"
include "pm3.2i.mm"
include "wss.mm"
include "issh3.mm"

theorem nlelshi
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nlelsh.1: |- T e. LinFn


  assert |- ( null ` T ) e. SH

  proof
    cT
    cnl
    cfv
    #
    csh
    wcel
    #
    c0v
    @0
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @3
    @4
    csm
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    cc
    wral
    #
    wa
    #
    @2
    c0v
    chil
    wcel
    #
    c0v
    cT
    cfv
    cc0
    wceq
    #
    ax-hv0cl
    cT
    nlelsh.1
    lnfn0i
    chil
    cc
    cT
    wf
    #
    @2
    @12
    @13
    wa
    wb
    cT
    nlelsh.1
    lnfnfi
    #
    c0v
    cT
    elnlfn
    ax-mp
    mpbir2an
    @7
    @10
    @6
    vx
    vy
    @0
    @0
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    #
    @5
    chil
    wcel
    #
    @5
    cT
    cfv
    #
    cc0
    wceq
    #
    @6
    @16
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    @19
    @17
    @0
    chil
    @3
    @0
    cT
    cdm
    #
    chil
    @0
    cT
    ccnv
    cc0
    csn
    #
    cima
    #
    @24
    @14
    @0
    @26
    wceq
    @15
    cT
    nlfnval
    ax-mp
    cT
    @25
    cnvimass
    eqsstri
    chil
    cc
    cT
    @15
    fdmi
    sseqtri
    #
    sseli
    #
    @0
    chil
    @4
    @27
    sseli
    #
    @3
    @4
    hvaddcl
    syl2an
    @18
    @20
    cc0
    cc0
    caddc
    co
    #
    cc0
    @18
    @20
    @3
    cT
    cfv
    #
    @4
    cT
    cfv
    #
    caddc
    co
    #
    @30
    @16
    @22
    @23
    @20
    @33
    wceq
    @17
    @28
    @29
    @3
    @4
    cT
    nlelsh.1
    lnfnaddi
    syl2an
    @16
    @17
    @31
    cc0
    @32
    cc0
    caddc
    @16
    @22
    @31
    cc0
    wceq
    #
    @14
    @16
    @22
    @34
    wa
    wb
    @15
    @3
    cT
    elnlfn
    ax-mp
    simprbi
    @17
    @23
    @32
    cc0
    wceq
    #
    @14
    @17
    @23
    @35
    wa
    wb
    @15
    @4
    cT
    elnlfn
    ax-mp
    simprbi
    #
    oveqan12d
    eqtrd
    00id
    syl6eq
    @14
    @6
    @19
    @21
    wa
    wb
    @15
    @5
    cT
    elnlfn
    ax-mp
    sylanbrc
    rgen2
    @9
    vx
    vy
    cc
    @0
    @3
    cc
    wcel
    #
    @17
    wa
    #
    @8
    chil
    wcel
    #
    @8
    cT
    cfv
    #
    cc0
    wceq
    #
    @9
    @17
    @37
    @23
    @39
    @29
    @3
    @4
    hvmulcl
    sylan2
    @38
    @40
    @3
    @32
    cmul
    co
    #
    cc0
    @17
    @37
    @23
    @40
    @42
    wceq
    @29
    @3
    @4
    cT
    nlelsh.1
    lnfnmuli
    sylan2
    @17
    @37
    @42
    @3
    cc0
    cmul
    co
    cc0
    @17
    @32
    cc0
    @3
    cmul
    @36
    oveq2d
    @3
    mul01
    sylan9eqr
    eqtrd
    @14
    @9
    @39
    @41
    wa
    wb
    @15
    @8
    cT
    elnlfn
    ax-mp
    sylanbrc
    rgen2
    pm3.2i
    @0
    chil
    wss
    @1
    @2
    @11
    wa
    wb
    @27
    vx
    vy
    @0
    issh3
    ax-mp
    mpbir2an
end
