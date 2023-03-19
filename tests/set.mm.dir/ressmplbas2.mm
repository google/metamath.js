include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cab.mm"
include "cin.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "csubrg.mm"
include "wcel.mm"
include "eqid.mm"
include "subrgpsr.mm"
include "syl2anc.mm"
include "subrgss.mm"
include "syl.mm"
include "df-ss.mm"
include "sylib.mm"
include "subrg0.mm"
include "breq2d.mm"
include "abbidv.mm"
include "ineq12d.mm"
include "eqcomd.mm"
include "crab.mm"
include "mplbas.mm"
include "dfrab3.mm"
include "eqtri.mm"
include "ineq2i.mm"
include "inass.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"

theorem ressmplbas2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  assume ressmpl.s: |- S = ( I mPoly R )
  assume ressmpl.h: |- H = ( R |`s T )
  assume ressmpl.u: |- U = ( I mPoly H )
  assume ressmpl.b: |- B = ( Base ` U )
  assume ressmpl.1: |- ( ph -> I e. V )
  assume ressmpl.2: |- ( ph -> T e. ( SubRing ` R ) )
  assume ressmplbas2.w: |- W = ( I mPwSer H )
  assume ressmplbas2.c: |- C = ( Base ` W )
  assume ressmplbas2.k: |- K = ( Base ` S )


  assert |- ( ph -> B = ( C i^i K ) )

  proof
    wph
    cC
    vf
    cv
    #
    cH
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vf
    cab
    #
    cin
    #
    cC
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cin
    #
    @0
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vf
    cab
    #
    cin
    #
    cB
    cC
    cK
    cin
    #
    wph
    @11
    @4
    wph
    @7
    cC
    @10
    @3
    wph
    cC
    @6
    wss
    #
    @7
    cC
    wceq
    wph
    cC
    @5
    csubrg
    cfv
    wcel
    #
    @13
    wph
    cI
    cV
    wcel
    cT
    cR
    csubrg
    cfv
    wcel
    #
    @14
    ressmpl.1
    ressmpl.2
    cC
    cR
    @5
    cT
    cW
    cH
    cI
    cV
    @5
    eqid
    #
    ressmpl.h
    ressmplbas2.w
    ressmplbas2.c
    subrgpsr
    syl2anc
    cC
    @6
    @5
    @6
    eqid
    #
    subrgss
    syl
    cC
    @6
    df-ss
    sylib
    wph
    @9
    @2
    vf
    wph
    @8
    @1
    @0
    cfsupp
    wph
    @15
    @8
    @1
    wceq
    ressmpl.2
    cT
    cR
    cH
    @8
    ressmpl.h
    @8
    eqid
    #
    subrg0
    syl
    breq2d
    abbidv
    ineq12d
    eqcomd
    cB
    @2
    vf
    cC
    crab
    @4
    cC
    cU
    cH
    cW
    cB
    vf
    cI
    @1
    ressmpl.u
    ressmplbas2.w
    ressmplbas2.c
    @1
    eqid
    ressmpl.b
    mplbas
    @2
    vf
    cC
    dfrab3
    eqtri
    @12
    cC
    @6
    @10
    cin
    #
    cin
    @11
    cK
    @19
    cC
    cK
    @9
    vf
    @6
    crab
    @19
    @6
    cS
    cR
    @5
    cK
    vf
    cI
    @8
    ressmpl.s
    @16
    @17
    @18
    ressmplbas2.k
    mplbas
    @9
    vf
    @6
    dfrab3
    eqtri
    ineq2i
    cC
    @6
    @10
    inass
    eqtr4i
    3eqtr4g
end
