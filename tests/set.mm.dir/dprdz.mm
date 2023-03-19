include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cmpt.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "ccntz.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "cv.mm"
include "0subg.mm"
include "ad2antrr.mm"
include "fmptd.mm"
include "wne.mm"
include "w3a.mm"
include "wss.mm"
include "cbs.mm"
include "grpidcl.mm"
include "adantr.mm"
include "snssd.mm"
include "cntzsubg.mm"
include "syldan.mm"
include "subg0cl.mm"
include "syl.mm"
include "simpr1.mm"
include "eqidd.mm"
include "snex.mm"
include "fvmpt3i.mm"
include "simpr2.mm"
include "fveq2d.mm"
include "3sstr4d.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "adantl.mm"
include "ineq1d.mm"
include "cmre.mm"
include "cacs.mm"
include "subgacs.mm"
include "acsmred.mm"
include "cpw.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "frn.mm"
include "mresspw.mm"
include "sstrd.mm"
include "syl5ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "df-ss.mm"
include "eqtrd.mm"
include "eqimss.mm"
include "dmdprdd.mm"
include "dmmptd.mm"
include "dprdlub.mm"
include "dprdsubg.mm"
include "3syl.mm"
include "eqssd.mm"
include "jca.mm"

theorem dprdz
  let vx: setvar x
  let cG: class G
  let cI: class I
  let cV: class V
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume dprd0.0: |- .0. = ( 0g ` G )

  disjoint .0. x
  disjoint G x
  disjoint I x
  disjoint V x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint G y
  disjoint G z
  disjoint I y
  disjoint I z
  disjoint V y
  disjoint V z
  assert |- ( ( G e. Grp /\ I e. V ) -> ( G dom DProd ( x e. I |-> { .0. } ) /\ ( G DProd ( x e. I |-> { .0. } ) ) = { .0. } ) )

  proof
    cG
    cgrp
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cG
    vx
    cI
    c.0
    csn
    #
    cmpt
    #
    cdprd
    cdm
    wbr
    #
    cG
    @4
    cdprd
    co
    #
    @3
    wceq
    @2
    vy
    vz
    @4
    cG
    cI
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cV
    c.0
    cG
    ccntz
    cfv
    #
    @9
    eqid
    #
    dprd0.0
    @8
    eqid
    #
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    vx
    cI
    @3
    @7
    @4
    @0
    @3
    @7
    wcel
    #
    @1
    vx
    cv
    #
    cI
    wcel
    cG
    c.0
    dprd0.0
    0subg
    #
    ad2antrr
    #
    @4
    eqid
    #
    fmptd
    #
    @2
    vy
    cv
    #
    cI
    wcel
    #
    vz
    cv
    #
    cI
    wcel
    #
    @18
    @20
    wne
    #
    w3a
    #
    wa
    #
    @3
    @3
    @9
    cfv
    #
    @18
    @4
    cfv
    #
    @20
    @4
    cfv
    #
    @9
    cfv
    @2
    @3
    @25
    wss
    @23
    @2
    c.0
    @25
    @2
    @25
    @7
    wcel
    #
    c.0
    @25
    wcel
    @0
    @1
    @3
    cG
    cbs
    cfv
    #
    wss
    @28
    @2
    c.0
    @29
    @0
    c.0
    @29
    wcel
    @1
    @29
    cG
    c.0
    @29
    eqid
    #
    dprd0.0
    grpidcl
    adantr
    snssd
    @29
    @3
    cG
    @9
    @30
    @10
    cntzsubg
    syldan
    @25
    cG
    c.0
    dprd0.0
    subg0cl
    syl
    snssd
    adantr
    @24
    @19
    @26
    @3
    wceq
    #
    @2
    @19
    @21
    @22
    simpr1
    vx
    @18
    @3
    @3
    cI
    @4
    @13
    @18
    wceq
    @3
    eqidd
    @16
    c.0
    snex
    #
    fvmpt3i
    #
    syl
    @24
    @27
    @3
    @9
    @24
    @21
    @27
    @3
    wceq
    @2
    @19
    @21
    @22
    simpr2
    vx
    @20
    @3
    @3
    cI
    @4
    @13
    @20
    wceq
    @3
    eqidd
    @16
    @32
    fvmpt3i
    syl
    fveq2d
    3sstr4d
    @2
    @19
    wa
    #
    @26
    @4
    cI
    @18
    csn
    cdif
    #
    cima
    #
    cuni
    #
    @8
    cfv
    #
    cin
    #
    @3
    wceq
    @39
    @3
    wss
    @34
    @39
    @3
    @38
    cin
    #
    @3
    @34
    @26
    @3
    @38
    @19
    @31
    @2
    @33
    adantl
    #
    ineq1d
    @34
    @3
    @38
    wss
    @40
    @3
    wceq
    @34
    c.0
    @38
    @34
    @38
    @7
    wcel
    #
    c.0
    @38
    wcel
    @34
    @7
    @29
    cmre
    cfv
    wcel
    #
    @37
    @29
    wss
    #
    @42
    @34
    @7
    @29
    @0
    @7
    @29
    cacs
    cfv
    wcel
    @1
    @19
    @29
    cG
    @30
    subgacs
    ad2antrr
    acsmred
    #
    @34
    @36
    @29
    cpw
    #
    wss
    @44
    @34
    @36
    @4
    crn
    #
    @46
    @4
    @35
    imassrn
    @34
    @47
    @7
    @46
    @34
    cI
    @7
    @4
    wf
    #
    @47
    @7
    wss
    @2
    @48
    @19
    @17
    adantr
    cI
    @7
    @4
    frn
    syl
    @34
    @43
    @7
    @46
    wss
    @45
    @7
    @29
    mresspw
    syl
    sstrd
    syl5ss
    @36
    @29
    sspwuni
    sylib
    @7
    @37
    @8
    @29
    @11
    mrccl
    syl2anc
    @38
    cG
    c.0
    dprd0.0
    subg0cl
    syl
    snssd
    @3
    @38
    df-ss
    sylib
    eqtrd
    @39
    @3
    eqimss
    syl
    dmdprdd
    #
    @2
    @6
    @3
    @2
    @4
    @3
    vy
    cG
    cI
    @49
    @2
    vx
    @4
    cI
    @3
    @7
    @16
    @15
    dmmptd
    @0
    @12
    @1
    @14
    adantr
    @34
    @31
    @26
    @3
    wss
    @41
    @26
    @3
    eqimss
    syl
    dprdlub
    @2
    c.0
    @6
    @2
    @5
    @6
    @7
    wcel
    c.0
    @6
    wcel
    @49
    @4
    cG
    dprdsubg
    @6
    cG
    c.0
    dprd0.0
    subg0cl
    3syl
    snssd
    eqssd
    jca
end
