include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "opelxpi.mm"
include "3adant1.mm"
include "fvres.mm"
include "syl.mm"
include "df-ov.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem rhmsubcALTVlem2
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume rngcrescrhmALTV.u: |- ( ph -> U e. V )
  assume rngcrescrhmALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcrescrhmALTV.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhmALTV.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ( ph /\ X e. R /\ Y e. R ) -> ( X H Y ) = ( X RingHom Y ) )

  proof
    wph
    cX
    cR
    wcel
    #
    cY
    cR
    wcel
    #
    w3a
    #
    cX
    cY
    cop
    #
    crh
    cR
    cR
    cxp
    #
    cres
    #
    cfv
    #
    @3
    crh
    cfv
    #
    cX
    cY
    cH
    co
    #
    cX
    cY
    crh
    co
    @2
    @3
    @4
    wcel
    #
    @6
    @7
    wceq
    @0
    @1
    @9
    wph
    cX
    cY
    cR
    cR
    opelxpi
    3adant1
    @3
    @4
    crh
    fvres
    syl
    @8
    @3
    cH
    cfv
    @6
    cX
    cY
    cH
    df-ov
    @3
    cH
    @5
    rngcrescrhmALTV.h
    fveq1i
    eqtri
    cX
    cY
    crh
    df-ov
    3eqtr4g
end
