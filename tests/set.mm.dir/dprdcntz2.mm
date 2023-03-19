include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cfv.mm"
include "cdm.mm"
include "wbr.mm"
include "wss.mm"
include "dprdres.mm"
include "simpld.mm"
include "cin.mm"
include "dmres.mm"
include "wceq.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "cgrp.mm"
include "wcel.mm"
include "cbs.mm"
include "csubg.mm"
include "dprdgrp.mm"
include "syl.mm"
include "eqid.mm"
include "dprdssv.mm"
include "cntzsubg.mm"
include "sylancl.mm"
include "cv.mm"
include "wa.mm"
include "fvres.mm"
include "adantl.mm"
include "adantr.mm"
include "dprdsubg.mm"
include "sselda.mm"
include "dprdf2.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "subgss.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "wn.mm"
include "wne.mm"
include "simpr.mm"
include "wi.mm"
include "c0.mm"
include "noel.mm"
include "elin.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "mtbiri.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "nelne2.mm"
include "dprdcntz.mm"
include "eqsstrd.mm"
include "dprdlub.mm"
include "cntzrecd.mm"

theorem dprdcntz2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cG: class G
  let cI: class I
  let cZ: class Z
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let c.0: class .0.
  assume dprdcntz2.1: |- ( ph -> G dom DProd S )
  assume dprdcntz2.2: |- ( ph -> dom S = I )
  assume dprdcntz2.c: |- ( ph -> C C_ I )
  assume dprdcntz2.d: |- ( ph -> D C_ I )
  assume dprdcntz2.i: |- ( ph -> ( C i^i D ) = (/) )
  assume dprdcntz2.z: |- Z = ( Cntz ` G )


  assert |- ( ph -> ( G DProd ( S |` C ) ) C_ ( Z ` ( G DProd ( S |` D ) ) ) )

  proof
    wph
    cS
    cC
    cres
    #
    cG
    cS
    cD
    cres
    #
    cdprd
    co
    #
    cZ
    cfv
    #
    vx
    cG
    cC
    wph
    cG
    @0
    cdprd
    cdm
    #
    wbr
    cG
    @0
    cdprd
    co
    cG
    cS
    cdprd
    co
    #
    wss
    wph
    cC
    cS
    cG
    cI
    dprdcntz2.1
    dprdcntz2.2
    dprdcntz2.c
    dprdres
    simpld
    wph
    @0
    cdm
    cC
    cS
    cdm
    #
    cin
    #
    cC
    cS
    cC
    dmres
    wph
    cC
    @6
    wss
    @7
    cC
    wceq
    wph
    cC
    cI
    @6
    dprdcntz2.c
    dprdcntz2.2
    sseqtr4d
    cC
    @6
    df-ss
    sylib
    syl5eq
    wph
    cG
    cgrp
    wcel
    #
    @2
    cG
    cbs
    cfv
    #
    wss
    @3
    cG
    csubg
    cfv
    #
    wcel
    wph
    cG
    cS
    @4
    wbr
    #
    @8
    dprdcntz2.1
    cS
    cG
    dprdgrp
    syl
    #
    @9
    @1
    cG
    @9
    eqid
    #
    dprdssv
    @9
    @2
    cG
    cZ
    @13
    dprdcntz2.z
    cntzsubg
    sylancl
    wph
    vx
    cv
    #
    cC
    wcel
    #
    wa
    #
    @14
    @0
    cfv
    #
    @14
    cS
    cfv
    #
    @3
    @15
    @17
    @18
    wceq
    wph
    @14
    cC
    cS
    fvres
    adantl
    @16
    @2
    @18
    cG
    cZ
    dprdcntz2.z
    @16
    cG
    @1
    @4
    wbr
    #
    @2
    @10
    wcel
    wph
    @19
    @15
    wph
    @19
    @2
    @5
    wss
    wph
    cD
    cS
    cG
    cI
    dprdcntz2.1
    dprdcntz2.2
    dprdcntz2.d
    dprdres
    simpld
    adantr
    #
    @1
    cG
    dprdsubg
    syl
    wph
    @15
    @14
    cI
    wcel
    #
    @18
    @10
    wcel
    #
    wph
    cC
    cI
    @14
    dprdcntz2.c
    sselda
    #
    wph
    cI
    @10
    @14
    cS
    wph
    cS
    cG
    cI
    dprdcntz2.1
    dprdcntz2.2
    dprdf2
    ffvelrnda
    syldan
    #
    @16
    @1
    @18
    cZ
    cfv
    #
    vy
    cG
    cD
    @20
    wph
    @1
    cdm
    #
    cD
    wceq
    @15
    wph
    @26
    cD
    @6
    cin
    #
    cD
    cS
    cD
    dmres
    wph
    cD
    @6
    wss
    @27
    cD
    wceq
    wph
    cD
    cI
    @6
    dprdcntz2.d
    dprdcntz2.2
    sseqtr4d
    cD
    @6
    df-ss
    sylib
    syl5eq
    adantr
    @16
    @8
    @18
    @9
    wss
    #
    @25
    @10
    wcel
    wph
    @8
    @15
    @12
    adantr
    @16
    @22
    @28
    @24
    @9
    @18
    cG
    @13
    subgss
    syl
    @9
    @18
    cG
    cZ
    @13
    dprdcntz2.z
    cntzsubg
    syl2anc
    @16
    vy
    cv
    #
    cD
    wcel
    #
    wa
    #
    @29
    @1
    cfv
    #
    @29
    cS
    cfv
    #
    @25
    @30
    @32
    @33
    wceq
    @16
    @29
    cD
    cS
    fvres
    adantl
    @31
    cS
    cG
    cI
    @29
    @14
    cZ
    wph
    @11
    @15
    @30
    dprdcntz2.1
    ad2antrr
    wph
    @6
    cI
    wceq
    @15
    @30
    dprdcntz2.2
    ad2antrr
    @16
    cD
    cI
    @29
    wph
    cD
    cI
    wss
    @15
    dprdcntz2.d
    adantr
    sselda
    @16
    @21
    @30
    @23
    adantr
    @31
    @30
    @14
    cD
    wcel
    #
    wn
    #
    @29
    @14
    wne
    @16
    @30
    simpr
    @16
    @35
    @30
    wph
    @15
    @35
    wph
    @15
    @34
    wa
    #
    wn
    @15
    @35
    wi
    wph
    @36
    @14
    c0
    wcel
    #
    @14
    noel
    @36
    @14
    cC
    cD
    cin
    #
    wcel
    wph
    @37
    @14
    cC
    cD
    elin
    wph
    @38
    c0
    @14
    dprdcntz2.i
    eleq2d
    syl5bbr
    mtbiri
    @15
    @34
    imnan
    sylibr
    imp
    adantr
    @29
    @14
    cD
    nelne2
    syl2anc
    dprdcntz2.z
    dprdcntz
    eqsstrd
    dprdlub
    cntzrecd
    eqsstrd
    dprdlub
end
