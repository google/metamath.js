include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cbs.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "cvv.mm"
include "cgrp.mm"
include "wa.mm"
include "eqid.mm"
include "grpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "psrelbas.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "fvex.mm"
include "elmap.mm"
include "sylibr.mm"
include "psradd.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "elbasov.mm"
include "syl.mm"
include "simpld.mm"
include "psrbas.mm"
include "3eltr4d.mm"

theorem psraddcl
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cI: class I
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume psraddcl.s: |- S = ( I mPwSer R )
  assume psraddcl.b: |- B = ( Base ` S )
  assume psraddcl.p: |- .+ = ( +g ` S )
  assume psraddcl.r: |- ( ph -> R e. Grp )
  assume psraddcl.x: |- ( ph -> X e. B )
  assume psraddcl.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .+ Y ) e. B )

  proof
    wph
    cX
    cY
    cR
    cplusg
    cfv
    #
    cof
    co
    #
    cR
    cbs
    cfv
    #
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
    cmap
    co
    #
    cX
    cY
    c.pl
    co
    cB
    wph
    @5
    @2
    @1
    wf
    @1
    @6
    wcel
    wph
    vx
    vy
    @5
    @5
    @5
    @0
    @2
    @2
    @2
    cX
    cY
    cvv
    cvv
    wph
    cR
    cgrp
    wcel
    #
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    @8
    @10
    @0
    co
    @2
    wcel
    #
    psraddcl.r
    @7
    @9
    @11
    @12
    @2
    @0
    cR
    @8
    @10
    @2
    eqid
    #
    @0
    eqid
    #
    grpcl
    3expb
    sylan
    wph
    cB
    @5
    cR
    cS
    vf
    cI
    @2
    cX
    psraddcl.s
    @13
    @5
    eqid
    #
    psraddcl.b
    psraddcl.x
    psrelbas
    wph
    cB
    @5
    cR
    cS
    vf
    cI
    @2
    cY
    psraddcl.s
    @13
    @15
    psraddcl.b
    psraddcl.y
    psrelbas
    @5
    cvv
    wcel
    wph
    @3
    vf
    @4
    cn0
    cI
    cmap
    ovex
    rabex
    #
    a1i
    #
    @17
    @5
    inidm
    off
    @2
    @5
    @1
    cR
    cbs
    fvex
    @16
    elmap
    sylibr
    wph
    cB
    @0
    c.pl
    cR
    cS
    cI
    cX
    cY
    psraddcl.s
    psraddcl.b
    @14
    psraddcl.p
    psraddcl.x
    psraddcl.y
    psradd
    wph
    cB
    @5
    cR
    cS
    vf
    cI
    @2
    cvv
    psraddcl.s
    @13
    @15
    psraddcl.b
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wph
    cX
    cB
    wcel
    @18
    @19
    wa
    psraddcl.x
    cX
    cB
    cS
    cmps
    cI
    cR
    reldmpsr
    psraddcl.s
    psraddcl.b
    elbasov
    syl
    simpld
    psrbas
    3eltr4d
end
