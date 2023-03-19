include "cvv.mm"
include "wcel.mm"
include "cconcat.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "frmdbas.mm"
include "eqid.mm"
include "frmdval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cword.mm"
include "wrdexg.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "ccatfn.mm"
include "xpss.mm"
include "fnssres.mm"
include "mp2an.mm"
include "wa.mm"
include "ovres.mm"
include "frmdelbas.mm"
include "ccatcl.mm"
include "syl2an.mm"
include "eqeltrd.mm"
include "rgen2a.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an12.mm"
include "grpplusg.mm"
include "3syl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "cfrmd.mm"
include "fvprc.mm"
include "res0.mm"
include "c2.mm"
include "df-plusg.mm"
include "str0.mm"
include "eqtr2i.mm"
include "syl6eq.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "reseq2d.mm"
include "pm2.61i.mm"

theorem frmdplusg
  let cB: class B
  let c.pl: class .+
  let cI: class I
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume frmdbas.m: |- M = ( freeMnd ` I )
  assume frmdbas.b: |- B = ( Base ` M )
  assume frmdplusg.p: |- .+ = ( +g ` M )


  assert |- .+ = ( ++ |` ( B X. B ) )

  proof
    cI
    cvv
    wcel
    #
    c.pl
    cconcat
    cB
    cB
    cxp
    #
    cres
    #
    wceq
    @0
    c.pl
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    @2
    cop
    cpr
    #
    cplusg
    cfv
    #
    @2
    @0
    c.pl
    cM
    cplusg
    cfv
    #
    @4
    frmdplusg.p
    @0
    cM
    @3
    cplusg
    cB
    @2
    cI
    cM
    cvv
    frmdbas.m
    cB
    cI
    cM
    cvv
    frmdbas.m
    frmdbas.b
    frmdbas
    @2
    eqid
    frmdval
    fveq2d
    syl5eq
    @0
    cI
    cword
    #
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @2
    @4
    wceq
    cI
    cvv
    wrdexg
    @1
    @6
    @2
    wf
    #
    @1
    cvv
    wcel
    @7
    @8
    @9
    @2
    @1
    wfn
    #
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    @6
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cconcat
    cvv
    cvv
    cxp
    #
    wfn
    @1
    @15
    wss
    @10
    ccatfn
    cB
    cB
    xpss
    @15
    @1
    cconcat
    fnssres
    mp2an
    @14
    vx
    vy
    cB
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    wa
    @13
    @11
    @12
    cconcat
    co
    #
    @6
    @11
    @12
    cB
    cB
    cconcat
    ovres
    @16
    @11
    @6
    wcel
    @12
    @6
    wcel
    @18
    @6
    wcel
    @17
    cB
    cI
    cM
    @11
    frmdbas.m
    frmdbas.b
    frmdelbas
    cB
    cI
    cM
    @12
    frmdbas.m
    frmdbas.b
    frmdelbas
    cI
    @11
    @12
    ccatcl
    syl2an
    eqeltrd
    rgen2a
    vx
    vy
    cB
    cB
    @6
    @2
    ffnov
    mpbir2an
    cB
    cB
    cB
    cM
    cbs
    cfv
    #
    cvv
    frmdbas.b
    cM
    cbs
    fvex
    eqeltri
    #
    @20
    xpex
    @1
    @6
    @2
    cvv
    cvv
    fex2
    mp3an12
    cB
    @2
    @3
    cvv
    @3
    eqid
    grpplusg
    3syl
    eqtr4d
    @0
    wn
    #
    c.pl
    cconcat
    c0
    cres
    #
    @2
    @21
    c.pl
    c0
    cplusg
    cfv
    #
    @22
    @21
    c.pl
    @5
    @23
    frmdplusg.p
    @21
    cM
    c0
    cplusg
    @21
    cM
    cI
    cfrmd
    cfv
    c0
    frmdbas.m
    cI
    cfrmd
    fvprc
    syl5eq
    #
    fveq2d
    syl5eq
    @22
    c0
    @23
    cconcat
    res0
    cplusg
    c2
    df-plusg
    str0
    eqtr2i
    syl6eq
    @21
    @1
    c0
    cconcat
    @21
    @1
    cB
    c0
    cxp
    c0
    @21
    cB
    c0
    cB
    @21
    @19
    c0
    cbs
    cfv
    cB
    c0
    @21
    cM
    c0
    cbs
    @24
    fveq2d
    frmdbas.b
    base0
    3eqtr4g
    xpeq2d
    cB
    xp0
    syl6eq
    reseq2d
    eqtr4d
    pm2.61i
end
