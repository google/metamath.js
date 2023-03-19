include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cof.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "psradd.mm"
include "cbs.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wss.mm"
include "cvv.mm"
include "fvex.mm"
include "csubrg.mm"
include "wceq.mm"
include "subrgbas.mm"
include "syl.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "mapss.mm"
include "sylancr.mm"
include "adantr.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "elbasov.mm"
include "ad2antrl.mm"
include "simpld.mm"
include "psrbas.mm"
include "3sstr4d.mm"
include "sseldd.mm"
include "ressplusg.mm"
include "ofeq.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "eqeltri.mm"
include "mp1i.mm"
include "3eqtr2d.mm"

theorem resspsradd
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vf: setvar f
  let vy: setvar y
  assume resspsr.s: |- S = ( I mPwSer R )
  assume resspsr.h: |- H = ( R |`s T )
  assume resspsr.u: |- U = ( I mPwSer H )
  assume resspsr.b: |- B = ( Base ` U )
  assume resspsr.p: |- P = ( S |`s B )
  assume resspsr.2: |- ( ph -> T e. ( SubRing ` R ) )


  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X ( +g ` U ) Y ) = ( X ( +g ` P ) Y ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cU
    cplusg
    cfv
    #
    co
    cX
    cY
    cH
    cplusg
    cfv
    #
    cof
    #
    co
    #
    cX
    cY
    cS
    cplusg
    cfv
    #
    co
    #
    cX
    cY
    cP
    cplusg
    cfv
    #
    co
    @3
    cB
    @5
    @4
    cH
    cU
    cI
    cX
    cY
    resspsr.u
    resspsr.b
    @5
    eqid
    @4
    eqid
    wph
    @0
    @1
    simprl
    #
    wph
    @0
    @1
    simprr
    #
    psradd
    @3
    @9
    cX
    cY
    cR
    cplusg
    cfv
    #
    cof
    #
    co
    @7
    @3
    cS
    cbs
    cfv
    #
    @13
    @8
    cR
    cS
    cI
    cX
    cY
    resspsr.s
    @15
    eqid
    #
    @13
    eqid
    #
    @8
    eqid
    #
    @3
    cB
    @15
    cX
    @3
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
    @20
    cmap
    co
    #
    cB
    @15
    wph
    @21
    @23
    wss
    #
    @2
    wph
    @22
    cvv
    wcel
    @19
    @22
    wss
    @24
    cR
    cbs
    fvex
    wph
    @19
    cT
    @22
    wph
    cT
    cR
    csubrg
    cfv
    #
    wcel
    #
    cT
    @19
    wceq
    resspsr.2
    cT
    cR
    cH
    resspsr.h
    subrgbas
    syl
    wph
    @26
    cT
    @22
    wss
    resspsr.2
    cT
    @22
    cR
    @22
    eqid
    #
    subrgss
    syl
    eqsstr3d
    @19
    @22
    @20
    cvv
    mapss
    sylancr
    adantr
    @3
    cB
    @20
    cH
    cU
    vf
    cI
    @19
    cvv
    resspsr.u
    @19
    eqid
    @20
    eqid
    #
    resspsr.b
    @3
    cI
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    @0
    @29
    @30
    wa
    wph
    @1
    cX
    cB
    cU
    cmps
    cI
    cH
    reldmpsr
    resspsr.u
    resspsr.b
    elbasov
    ad2antrl
    simpld
    #
    psrbas
    @3
    @15
    @20
    cR
    cS
    vf
    cI
    @22
    cvv
    resspsr.s
    @27
    @28
    @16
    @31
    psrbas
    3sstr4d
    #
    @11
    sseldd
    @3
    cB
    @15
    cY
    @32
    @12
    sseldd
    psradd
    @3
    @14
    @6
    cX
    cY
    @3
    @13
    @5
    wceq
    #
    @14
    @6
    wceq
    wph
    @33
    @2
    wph
    @26
    @33
    resspsr.2
    cT
    @13
    cR
    cH
    @25
    resspsr.h
    @17
    ressplusg
    syl
    adantr
    @13
    @5
    ofeq
    syl
    oveqd
    eqtrd
    @3
    @8
    @10
    cX
    cY
    cB
    cvv
    wcel
    @8
    @10
    wceq
    @3
    cB
    cU
    cbs
    cfv
    cvv
    resspsr.b
    cU
    cbs
    fvex
    eqeltri
    cB
    @8
    cS
    cP
    cvv
    resspsr.p
    @18
    ressplusg
    mp1i
    oveqd
    3eqtr2d
end
