include "crh.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "simpl.mm"
include "wfn.mm"
include "wb.mm"
include "f1fn.mm"
include "adantl.mm"
include "elpreima.mm"
include "syl.mm"
include "biimpa.mm"
include "simpld.mm"
include "simprd.mm"
include "fvex.mm"
include "elsn.mm"
include "sylib.mm"
include "wi.mm"
include "w3a.mm"
include "f1rhm0to0.mm"
include "biimpd.mm"
include "3expa.mm"
include "imp.mm"
include "syl21anc.mm"
include "ex.mm"
include "velsn.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "wss.mm"
include "crg.mm"
include "cgrp.mm"
include "rhmrcl1.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmid.mm"
include "sylibr.mm"
include "wf.mm"
include "rhmf.mm"
include "ffn.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "adantr.mm"
include "eqssd.mm"
include "wral.mm"
include "csg.mm"
include "simpr2l.mm"
include "simpr2r.mm"
include "simpr3.mm"
include "eqid.mm"
include "ghmeqker.mm"
include "syl31anc.mm"
include "simpr1.mm"
include "eleqtrd.mm"
include "ovex.mm"
include "grpsubeq0.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "3anassrs.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem kerf1hrm
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume kerf1hrm.a: |- A = ( Base ` R )
  assume kerf1hrm.b: |- B = ( Base ` S )
  assume kerf1hrm.n: |- N = ( 0g ` R )
  assume kerf1hrm.0: |- .0. = ( 0g ` S )


  assert |- ( F e. ( R RingHom S ) -> ( F : A -1-1-> B <-> ( `' F " { .0. } ) = { N } ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    cF
    ccnv
    c.0
    csn
    #
    cima
    #
    cN
    csn
    #
    wceq
    #
    @0
    @1
    wa
    #
    @3
    @4
    @6
    vx
    @3
    @4
    @6
    vx
    cv
    #
    @3
    wcel
    #
    @7
    cN
    wceq
    #
    @7
    @4
    wcel
    @6
    @8
    @9
    @6
    @8
    wa
    #
    @6
    @7
    cA
    wcel
    #
    @7
    cF
    cfv
    #
    c.0
    wceq
    #
    @9
    @6
    @8
    simpl
    @10
    @11
    @12
    @2
    wcel
    #
    @6
    @8
    @11
    @14
    wa
    #
    @6
    cF
    cA
    wfn
    #
    @8
    @15
    wb
    @1
    @16
    @0
    cA
    cB
    cF
    f1fn
    adantl
    cA
    @7
    @2
    cF
    elpreima
    syl
    biimpa
    #
    simpld
    @10
    @14
    @13
    @10
    @11
    @14
    @17
    simprd
    @12
    c.0
    @7
    cF
    fvex
    elsn
    sylib
    @6
    @11
    wa
    @13
    @9
    @0
    @1
    @11
    @13
    @9
    wi
    @0
    @1
    @11
    w3a
    @13
    @9
    cA
    cB
    cR
    cS
    cF
    c.0
    @7
    cN
    kerf1hrm.a
    kerf1hrm.b
    kerf1hrm.0
    kerf1hrm.n
    f1rhm0to0
    biimpd
    3expa
    imp
    syl21anc
    ex
    vx
    cN
    velsn
    syl6ibr
    ssrdv
    @0
    @4
    @3
    wss
    @1
    @0
    cN
    @3
    @0
    cN
    @3
    wcel
    #
    cN
    cA
    wcel
    #
    cN
    cF
    cfv
    #
    @2
    wcel
    #
    @0
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    #
    @19
    cR
    cS
    cF
    rhmrcl1
    #
    cR
    ringgrp
    #
    cA
    cR
    cN
    kerf1hrm.a
    kerf1hrm.n
    grpidcl
    3syl
    @0
    @20
    c.0
    wceq
    #
    @21
    @0
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    @26
    cR
    cS
    cF
    rhmghm
    #
    cR
    cS
    cF
    cN
    c.0
    kerf1hrm.n
    kerf1hrm.0
    ghmid
    syl
    @20
    c.0
    cN
    cF
    fvex
    elsn
    sylibr
    @0
    cA
    cB
    cF
    wf
    #
    @16
    @18
    @19
    @21
    wa
    wb
    cA
    cB
    cR
    cS
    cF
    kerf1hrm.a
    kerf1hrm.b
    rhmf
    #
    cA
    cB
    cF
    ffn
    cA
    cN
    @2
    cF
    elpreima
    3syl
    mpbir2and
    snssd
    adantr
    eqssd
    @0
    @5
    wa
    #
    @29
    @12
    vy
    cv
    #
    cF
    cfv
    wceq
    #
    @7
    @32
    wceq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @1
    @0
    @29
    @5
    @30
    adantr
    @31
    @35
    vx
    vy
    cA
    cA
    @31
    @11
    @32
    cA
    wcel
    #
    wa
    #
    wa
    @33
    @34
    @0
    @5
    @37
    @33
    @34
    @0
    @5
    @37
    @33
    w3a
    #
    wa
    #
    @7
    @32
    cR
    csg
    cfv
    #
    co
    #
    cN
    wceq
    #
    @34
    @39
    @41
    @4
    wcel
    @42
    @39
    @41
    @3
    @4
    @39
    @27
    @11
    @36
    @33
    @41
    @3
    wcel
    #
    @0
    @27
    @38
    @28
    adantr
    @11
    @36
    @5
    @33
    @0
    simpr2l
    #
    @11
    @36
    @5
    @33
    @0
    simpr2r
    #
    @0
    @5
    @37
    @33
    simpr3
    @27
    @11
    @36
    w3a
    @33
    @43
    cA
    cR
    cS
    @7
    cF
    @3
    @40
    @32
    c.0
    kerf1hrm.a
    kerf1hrm.0
    @3
    eqid
    @40
    eqid
    #
    ghmeqker
    biimpa
    syl31anc
    @0
    @5
    @37
    @33
    simpr1
    eleqtrd
    @41
    cN
    @7
    @32
    @40
    ovex
    elsn
    sylib
    @39
    @23
    @11
    @36
    @42
    @34
    wb
    @39
    @22
    @23
    @0
    @22
    @38
    @24
    adantr
    @25
    syl
    @44
    @45
    cA
    cR
    @40
    @7
    @32
    cN
    kerf1hrm.a
    kerf1hrm.n
    @46
    grpsubeq0
    syl3anc
    mpbid
    3anassrs
    ex
    ralrimivva
    vx
    vy
    cA
    cB
    cF
    dff13
    sylanbrc
    impbida
end
