include "cun.mm"
include "coch.mm"
include "cfv.mm"
include "co.mm"
include "uncom.mm"
include "fveq2i.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "djhval2.mm"
include "syl3anc.mm"
include "3eqtr4a.mm"

theorem djhcom
  let wph: wff ph
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhcom.h: |- H = ( LHyp ` K )
  assume djhcom.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhcom.v: |- V = ( Base ` U )
  assume djhcom.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhcom.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhcom.x: |- ( ph -> X C_ V )
  assume djhcom.y: |- ( ph -> Y C_ V )


  assert |- ( ph -> ( X .\/ Y ) = ( Y .\/ X ) )

  proof
    wph
    cX
    cY
    cun
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @1
    cfv
    #
    cY
    cX
    cun
    #
    @1
    cfv
    #
    @1
    cfv
    #
    cX
    cY
    c.or
    co
    #
    cY
    cX
    c.or
    co
    #
    @2
    @5
    @1
    @0
    @4
    @1
    cX
    cY
    uncom
    fveq2i
    fveq2i
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    cY
    cV
    wss
    #
    @7
    @3
    wceq
    djhcom.k
    djhcom.x
    djhcom.y
    cU
    cH
    c.or
    cK
    @1
    cV
    cW
    cX
    cY
    djhcom.h
    djhcom.u
    djhcom.v
    @1
    eqid
    #
    djhcom.j
    djhval2
    syl3anc
    wph
    @9
    @11
    @10
    @8
    @6
    wceq
    djhcom.k
    djhcom.y
    djhcom.x
    cU
    cH
    c.or
    cK
    @1
    cV
    cW
    cY
    cX
    djhcom.h
    djhcom.u
    djhcom.v
    @12
    djhcom.j
    djhval2
    syl3anc
    3eqtr4a
end
