include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "fvex.mm"
include "csubrg.mm"
include "subrgbas.mm"
include "syl.mm"
include "eqid.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "adantr.mm"
include "mapss.mm"
include "sylancr.mm"
include "simpr.mm"
include "psrbas.mm"
include "3sstr4d.mm"
include "wn.mm"
include "c0.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "ovprc1.mm"
include "syl5eq.mm"
include "adantl.mm"
include "fveq2d.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61dan.mm"
include "ressbas2.mm"

theorem resspsrbas
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let vk: setvar k
  let vx: setvar x
  let vf: setvar f
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume resspsr.s: |- S = ( I mPwSer R )
  assume resspsr.h: |- H = ( R |`s T )
  assume resspsr.u: |- U = ( I mPwSer H )
  assume resspsr.b: |- B = ( Base ` U )
  assume resspsr.p: |- P = ( S |`s B )
  assume resspsr.2: |- ( ph -> T e. ( SubRing ` R ) )


  assert |- ( ph -> B = ( Base ` P ) )

  proof
    wph
    cB
    cS
    cbs
    cfv
    #
    wss
    #
    cB
    cP
    cbs
    cfv
    wceq
    wph
    cI
    cvv
    wcel
    #
    @1
    wph
    @2
    wa
    #
    cH
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
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    cmap
    co
    #
    cR
    cbs
    cfv
    #
    @5
    cmap
    co
    #
    cB
    @0
    @3
    @7
    cvv
    wcel
    @4
    @7
    wss
    #
    @6
    @8
    wss
    cR
    cbs
    fvex
    wph
    @9
    @2
    wph
    @4
    cT
    @7
    wph
    cT
    cR
    csubrg
    cfv
    wcel
    #
    cT
    @4
    wceq
    resspsr.2
    cT
    cR
    cH
    resspsr.h
    subrgbas
    syl
    wph
    @10
    cT
    @7
    wss
    resspsr.2
    cT
    @7
    cR
    @7
    eqid
    #
    subrgss
    syl
    eqsstr3d
    adantr
    @4
    @7
    @5
    cvv
    mapss
    sylancr
    @3
    cB
    @5
    cH
    cU
    vf
    cI
    @4
    cvv
    resspsr.u
    @4
    eqid
    @5
    eqid
    #
    resspsr.b
    wph
    @2
    simpr
    #
    psrbas
    @3
    @0
    @5
    cR
    cS
    vf
    cI
    @7
    cvv
    resspsr.s
    @11
    @12
    @0
    eqid
    #
    @13
    psrbas
    3sstr4d
    wph
    @2
    wn
    #
    wa
    #
    cB
    c0
    @0
    @16
    cU
    cbs
    cfv
    c0
    cbs
    cfv
    cB
    c0
    @16
    cU
    c0
    cbs
    @15
    cU
    c0
    wceq
    wph
    @15
    cU
    cI
    cH
    cmps
    co
    c0
    resspsr.u
    cI
    cH
    cmps
    reldmpsr
    ovprc1
    syl5eq
    adantl
    fveq2d
    resspsr.b
    base0
    3eqtr4g
    @0
    0ss
    syl6eqss
    pm2.61dan
    cB
    @0
    cP
    cS
    resspsr.p
    @14
    ressbas2
    syl
end
