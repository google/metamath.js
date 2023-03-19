include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cmulr.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "csn.mm"
include "cts.mm"
include "ctopn.mm"
include "cpt.mm"
include "cun.mm"
include "eqid.mm"
include "simpl.mm"
include "psrbas.mm"
include "eqidd.mm"
include "simpr.mm"
include "psrval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "ofexg.mm"
include "c1.mm"
include "c9.mm"
include "psrvalstr.mm"
include "plusgid.mm"
include "snsstp2.mm"
include "ssun1.mm"
include "sstri.mm"
include "strfv.mm"
include "mp2b.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "ovprc.mm"
include "syl5eq.mm"
include "str0.mm"
include "base0.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "res0.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem psrplusg
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let vh: setvar h
  let vy: setvar y
  let wph: wff ph
  assume psrplusg.s: |- S = ( I mPwSer R )
  assume psrplusg.b: |- B = ( Base ` S )
  assume psrplusg.a: |- .+ = ( +g ` R )
  assume psrplusg.p: |- .+b = ( +g ` S )


  assert |- .+b = ( oF .+ |` ( B X. B ) )

  proof
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    c.pb
    c.pl
    cof
    #
    cB
    cB
    cxp
    #
    cres
    #
    wceq
    @2
    cS
    cplusg
    cfv
    #
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    @5
    cop
    #
    cnx
    cmulr
    cfv
    vf
    vg
    cB
    cB
    vk
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    crab
    #
    cR
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    vy
    @10
    crab
    vx
    cv
    #
    vf
    cv
    #
    cfv
    @11
    @12
    cmin
    cof
    co
    vg
    cv
    cfv
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    cmpt
    cmpt2
    #
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    cR
    cop
    cnx
    cvsca
    cfv
    vx
    vf
    cR
    cbs
    cfv
    #
    cB
    @10
    @12
    csn
    cxp
    @13
    @14
    cof
    co
    cmpt2
    #
    cop
    cnx
    cts
    cfv
    @10
    cR
    ctopn
    cfv
    #
    csn
    cxp
    cpt
    cfv
    #
    cop
    ctp
    #
    cun
    #
    cplusg
    cfv
    #
    c.pb
    @5
    @2
    cS
    @23
    cplusg
    @2
    vx
    vy
    cB
    @10
    c.pl
    @5
    cR
    cS
    @19
    @14
    @15
    vf
    vg
    vh
    vk
    cI
    @21
    @18
    @20
    cvv
    cvv
    psrplusg.s
    @18
    eqid
    #
    psrplusg.a
    @14
    eqid
    @20
    eqid
    @10
    eqid
    #
    @2
    cB
    @10
    cR
    cS
    vh
    cI
    @18
    cvv
    psrplusg.s
    @25
    @26
    psrplusg.b
    @0
    @1
    simpl
    #
    psrbas
    @5
    eqid
    @15
    eqid
    @19
    eqid
    @2
    @21
    eqidd
    @27
    @0
    @1
    simpr
    psrval
    fveq2d
    psrplusg.p
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @5
    @24
    wceq
    cB
    cB
    cB
    cS
    cbs
    cfv
    #
    cvv
    psrplusg.b
    cS
    cbs
    fvex
    eqeltri
    #
    @29
    xpex
    @4
    c.pl
    cvv
    ofexg
    @5
    @23
    cplusg
    cvv
    c1
    c9
    cop
    cB
    @5
    cR
    @19
    @15
    @21
    psrvalstr
    plusgid
    @9
    csn
    @17
    @23
    @7
    @9
    @16
    snsstp2
    @17
    @22
    ssun1
    sstri
    strfv
    mp2b
    3eqtr4g
    @2
    wn
    #
    c.pb
    c0
    @5
    @30
    @6
    c0
    cplusg
    cfv
    c.pb
    c0
    @30
    cS
    c0
    cplusg
    @30
    cS
    cI
    cR
    cmps
    co
    c0
    psrplusg.s
    cI
    cR
    cmps
    reldmpsr
    ovprc
    syl5eq
    #
    fveq2d
    psrplusg.p
    cplusg
    @8
    plusgid
    str0
    3eqtr4g
    @30
    @5
    @3
    c0
    cres
    c0
    @30
    @4
    c0
    @3
    @30
    @4
    cB
    c0
    cxp
    c0
    @30
    cB
    c0
    cB
    @30
    @28
    c0
    cbs
    cfv
    cB
    c0
    @30
    cS
    c0
    cbs
    @31
    fveq2d
    psrplusg.b
    base0
    3eqtr4g
    xpeq2d
    cB
    xp0
    syl6eq
    reseq2d
    @3
    res0
    syl6eq
    eqtr4d
    pm2.61i
end
