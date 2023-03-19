include "wcel.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "cbs.mm"
include "eqid.mm"
include "simprl.mm"
include "csubrg.mm"
include "wceq.mm"
include "adantr.mm"
include "subrgbas.mm"
include "syl.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "psrvsca.mm"
include "wss.mm"
include "subrgss.mm"
include "sseldd.mm"
include "resspsrbas.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "ressmulr.mm"
include "ofeq.mm"
include "3syl.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressvsca.mm"
include "mp1i.mm"
include "3eqtr2d.mm"

theorem resspsrvsca
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


  assert |- ( ( ph /\ ( X e. T /\ Y e. B ) ) -> ( X ( .s ` U ) Y ) = ( X ( .s ` P ) Y ) )

  proof
    wph
    cX
    cT
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
    cvsca
    cfv
    #
    co
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
    cX
    csn
    cxp
    #
    cY
    cH
    cmulr
    cfv
    #
    cof
    #
    co
    #
    cX
    cY
    cS
    cvsca
    cfv
    #
    co
    #
    cX
    cY
    cP
    cvsca
    cfv
    #
    co
    @3
    cB
    @5
    cH
    cU
    @4
    @7
    vf
    cY
    cI
    cH
    cbs
    cfv
    #
    cX
    resspsr.u
    @4
    eqid
    @13
    eqid
    resspsr.b
    @7
    eqid
    @5
    eqid
    #
    @3
    cX
    cT
    @13
    wph
    @0
    @1
    simprl
    #
    @3
    cT
    cR
    csubrg
    cfv
    #
    wcel
    #
    cT
    @13
    wceq
    wph
    @17
    @2
    resspsr.2
    adantr
    #
    cT
    cR
    cH
    resspsr.h
    subrgbas
    syl
    eleqtrd
    wph
    @0
    @1
    simprr
    #
    psrvsca
    @3
    @11
    @6
    cY
    cR
    cmulr
    cfv
    #
    cof
    #
    co
    @9
    @3
    cS
    cbs
    cfv
    #
    @5
    cR
    cS
    @10
    @20
    vf
    cY
    cI
    cR
    cbs
    cfv
    #
    cX
    resspsr.s
    @10
    eqid
    #
    @23
    eqid
    #
    @22
    eqid
    #
    @20
    eqid
    #
    @14
    @3
    cT
    @23
    cX
    @3
    @17
    cT
    @23
    wss
    @18
    cT
    @23
    cR
    @25
    subrgss
    syl
    @15
    sseldd
    @3
    cB
    @22
    cY
    wph
    cB
    @22
    wss
    @2
    wph
    cB
    cP
    cbs
    cfv
    @22
    wph
    cB
    cP
    cR
    cS
    cT
    cU
    cH
    cI
    resspsr.s
    resspsr.h
    resspsr.u
    resspsr.b
    resspsr.p
    resspsr.2
    resspsrbas
    cB
    @22
    cP
    cS
    resspsr.p
    @26
    ressbasss
    syl6eqss
    adantr
    @19
    sseldd
    psrvsca
    @3
    @21
    @8
    @6
    cY
    @3
    @17
    @20
    @7
    wceq
    @21
    @8
    wceq
    @18
    cT
    cR
    cH
    @20
    @16
    resspsr.h
    @27
    ressmulr
    @20
    @7
    ofeq
    3syl
    oveqd
    eqtrd
    @3
    @10
    @12
    cX
    cY
    cB
    cvv
    wcel
    @10
    @12
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
    @10
    cS
    cP
    cvv
    resspsr.p
    @24
    ressvsca
    mp1i
    oveqd
    3eqtr2d
end
