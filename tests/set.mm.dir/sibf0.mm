include "cdm.mm"
include "cuni.mm"
include "csn.mm"
include "cxp.mm"
include "csitg.mm"
include "co.mm"
include "wcel.mm"
include "cmbfm.mm"
include "crn.mm"
include "cfn.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cdif.mm"
include "wral.mm"
include "cmeas.mm"
include "csiga.mm"
include "dmmeas.mm"
include "syl.mm"
include "csigagen.mm"
include "cvv.mm"
include "ctopn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "sgsiga.mm"
include "syl5eqel.mm"
include "cmpt.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "cmnd.mm"
include "mndidcl.mm"
include "ctps.mm"
include "tpsuni.mm"
include "unieqi.mm"
include "unisg.mm"
include "mp1i.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "eleqtrd.mm"
include "mbfmcst.mm"
include "c0.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "wne.mm"
include "rnxp.mm"
include "snfi.mm"
include "pm2.61ine.mm"
include "noel.mm"
include "difeq1d.mm"
include "0dif.mm"
include "difid.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "issibf.mm"
include "mpbir3and.mm"

theorem sibf0
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vf: setvar f
  let vm: setvar m
  let vw: setvar w
  let vg: setvar g
  let cF: class F
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sibf0.1: |- ( ph -> W e. TopSp )
  assume sibf0.2: |- ( ph -> W e. Mnd )


  assert |- ( ph -> ( U. dom M X. { .0. } ) e. dom ( W sitg M ) )

  proof
    wph
    cM
    cdm
    #
    cuni
    #
    c.0
    csn
    #
    cxp
    #
    cW
    cM
    csitg
    co
    cdm
    wcel
    @3
    @0
    cS
    cmbfm
    co
    wcel
    @3
    crn
    #
    cfn
    wcel
    #
    @3
    ccnv
    vx
    cv
    #
    csn
    cima
    cM
    cfv
    cc0
    cpnf
    cico
    co
    wcel
    #
    vx
    @4
    @2
    cdif
    #
    wral
    wph
    vx
    c.0
    @0
    cS
    @3
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    @0
    csiga
    crn
    cuni
    #
    wcel
    sitgval.2
    cM
    dmmeas
    syl
    wph
    cS
    cJ
    csigagen
    cfv
    #
    @9
    sitgval.s
    wph
    cJ
    cvv
    cJ
    cvv
    wcel
    #
    wph
    cJ
    cW
    ctopn
    cfv
    cvv
    sitgval.j
    cW
    ctopn
    fvex
    eqeltri
    #
    a1i
    sgsiga
    syl5eqel
    @3
    vx
    @1
    c.0
    cmpt
    wceq
    wph
    vx
    @1
    c.0
    fconstmpt
    a1i
    wph
    c.0
    cB
    cS
    cuni
    #
    wph
    cW
    cmnd
    wcel
    c.0
    cB
    wcel
    sibf0.2
    cB
    cW
    c.0
    sitgval.b
    sitgval.0
    mndidcl
    syl
    wph
    cB
    cJ
    cuni
    #
    @13
    wph
    cW
    ctps
    wcel
    cB
    @14
    wceq
    sibf0.1
    cB
    cJ
    cW
    sitgval.b
    sitgval.j
    tpsuni
    syl
    wph
    @13
    @10
    cuni
    #
    @14
    cS
    @10
    sitgval.s
    unieqi
    @11
    @15
    @14
    wceq
    wph
    @12
    cJ
    cvv
    unisg
    mp1i
    syl5eq
    eqtr4d
    eleqtrd
    mbfmcst
    @5
    wph
    @5
    @1
    c0
    @1
    c0
    wceq
    #
    @4
    c0
    cfn
    @16
    @4
    c0
    crn
    c0
    @16
    @3
    c0
    @16
    @3
    c0
    @2
    cxp
    c0
    @1
    c0
    @2
    xpeq1
    @2
    0xp
    syl6eq
    rneqd
    rn0
    syl6eq
    #
    0fin
    syl6eqel
    @1
    c0
    wne
    #
    @4
    @2
    cfn
    @1
    @2
    rnxp
    #
    c.0
    snfi
    syl6eqel
    pm2.61ine
    a1i
    wph
    @7
    vx
    @8
    @6
    @8
    wcel
    #
    @7
    wph
    @20
    @7
    @20
    @6
    c0
    wcel
    @6
    noel
    @8
    c0
    @6
    @8
    c0
    wceq
    @1
    c0
    @16
    @8
    c0
    @2
    cdif
    c0
    @16
    @4
    c0
    @2
    @17
    difeq1d
    @2
    0dif
    syl6eq
    @18
    @8
    @2
    @2
    cdif
    c0
    @18
    @4
    @2
    @2
    @19
    difeq1d
    @2
    difid
    syl6eq
    pm2.61ine
    eleq2i
    mtbir
    pm2.21i
    adantl
    ralrimiva
    wph
    vx
    cB
    cS
    c.x
    @3
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    issibf
    mpbir3and
end
