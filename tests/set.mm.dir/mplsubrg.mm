include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "crg.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "mplsubg.mm"
include "cbs.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "psrring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "psr1.mm"
include "cvv.mm"
include "wfun.mm"
include "w3a.mm"
include "csupp.mm"
include "wss.mm"
include "ovex.mm"
include "mptrabex.mm"
include "funmpt.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "a1i.mm"
include "snfi.mm"
include "cdif.mm"
include "wa.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "ifnefalse.mm"
include "rabex.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "eqbrtrd.mm"
include "mplelbas.mm"
include "sylanbrc.mm"
include "caddc.mm"
include "cof.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "mplsubrglem.mm"
include "ralrimivva.mm"
include "wb.mm"
include "issubrg2.mm"
include "mpbir3and.mm"

theorem mplsubrg
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cW: class W
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cD: class D
  let cX: class X
  let cY: class Y
  let c.x: class .x.
  let c.0: class .0.
  assume mplsubg.s: |- S = ( I mPwSer R )
  assume mplsubg.p: |- P = ( I mPoly R )
  assume mplsubg.u: |- U = ( Base ` P )
  assume mplsubg.i: |- ( ph -> I e. W )
  assume mpllss.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> U e. ( SubRing ` S ) )

  proof
    wph
    cU
    cS
    csubrg
    cfv
    wcel
    #
    cU
    cS
    csubg
    cfv
    wcel
    #
    cS
    cur
    cfv
    #
    cU
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cmulr
    cfv
    #
    co
    cU
    wcel
    #
    vy
    cU
    wral
    vx
    cU
    wral
    #
    wph
    cP
    cR
    cS
    cU
    cI
    cW
    mplsubg.s
    mplsubg.p
    mplsubg.u
    mplsubg.i
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    mpllss.r
    cR
    ringgrp
    syl
    mplsubg
    wph
    @2
    cS
    cbs
    cfv
    #
    wcel
    #
    @2
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    @3
    wph
    cS
    crg
    wcel
    #
    @11
    wph
    cR
    cS
    cI
    cW
    mplsubg.s
    mplsubg.i
    mpllss.r
    psrring
    #
    @10
    cS
    @2
    @10
    eqid
    #
    @2
    eqid
    #
    ringidcl
    syl
    wph
    @2
    vk
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vf
    cn0
    cI
    cmap
    co
    #
    crab
    #
    vk
    cv
    #
    cI
    cc0
    csn
    cxp
    #
    wceq
    cR
    cur
    cfv
    #
    @12
    cif
    #
    cmpt
    #
    @12
    cfsupp
    wph
    vk
    @19
    cR
    cS
    @2
    @22
    vf
    cI
    cW
    @12
    mplsubg.s
    mplsubg.i
    mpllss.r
    @19
    eqid
    #
    @12
    eqid
    #
    @22
    eqid
    @16
    psr1
    wph
    @24
    cvv
    wcel
    #
    @24
    wfun
    #
    @12
    cvv
    wcel
    #
    w3a
    #
    @21
    csn
    #
    cfn
    wcel
    #
    @24
    @12
    csupp
    co
    @31
    wss
    @24
    @12
    cfsupp
    wbr
    @30
    wph
    @27
    @28
    @29
    @17
    vk
    vf
    @18
    @23
    cn0
    cI
    cmap
    ovex
    #
    mptrabex
    vk
    @19
    @23
    funmpt
    cR
    c0g
    fvex
    3pm3.2i
    a1i
    @32
    wph
    @21
    snfi
    a1i
    wph
    @19
    @23
    vk
    cvv
    @31
    @12
    wph
    @20
    @19
    @31
    cdif
    wcel
    #
    wa
    @20
    @21
    wne
    #
    @23
    @12
    wceq
    @34
    @35
    wph
    @20
    @19
    @21
    eldifsni
    adantl
    @20
    @21
    @22
    @12
    ifnefalse
    syl
    @19
    cvv
    wcel
    wph
    @17
    vf
    @18
    @33
    rabex
    a1i
    suppss2
    @31
    @24
    cvv
    cvv
    @12
    suppssfifsupp
    syl12anc
    eqbrtrd
    @10
    cP
    cR
    cS
    cU
    cI
    @2
    @12
    mplsubg.p
    mplsubg.s
    @15
    @26
    mplsubg.u
    mplelbas
    sylanbrc
    wph
    @7
    vx
    vy
    cU
    cU
    wph
    @4
    cU
    wcel
    #
    @5
    cU
    wcel
    #
    wa
    #
    wa
    caddc
    cof
    @4
    @12
    csupp
    co
    @5
    @12
    csupp
    co
    cxp
    cima
    #
    @19
    cP
    cR
    cS
    cR
    cmulr
    cfv
    #
    cU
    vf
    cI
    cW
    @4
    @5
    @12
    mplsubg.s
    mplsubg.p
    mplsubg.u
    wph
    cI
    cW
    wcel
    @38
    mplsubg.i
    adantr
    wph
    @9
    @38
    mpllss.r
    adantr
    @25
    @26
    @39
    eqid
    @40
    eqid
    wph
    @36
    @37
    simprl
    wph
    @36
    @37
    simprr
    mplsubrglem
    ralrimivva
    wph
    @13
    @0
    @1
    @3
    @8
    w3a
    wb
    @14
    vx
    vy
    cU
    @10
    cS
    @6
    @2
    @15
    @16
    @6
    eqid
    issubrg2
    syl
    mpbir3and
end
