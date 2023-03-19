include "cun.mm"
include "cfv.mm"
include "coch.mm"
include "co.mm"
include "eqid.mm"
include "unssd.mm"
include "dochspss.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "djhval2.mm"
include "syl3anc.mm"
include "sseqtr4d.mm"

theorem djhspss
  let wph: wff ph
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhspss.h: |- H = ( LHyp ` K )
  assume djhspss.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhspss.v: |- V = ( Base ` U )
  assume djhspss.n: |- N = ( LSpan ` U )
  assume djhspss.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhspss.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhspss.x: |- ( ph -> X C_ V )
  assume djhspss.y: |- ( ph -> Y C_ V )


  assert |- ( ph -> ( N ` ( X u. Y ) ) C_ ( X .\/ Y ) )

  proof
    wph
    cX
    cY
    cun
    #
    cN
    cfv
    @0
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    @1
    cfv
    #
    cX
    cY
    c.or
    co
    #
    wph
    cU
    cH
    cK
    cN
    @1
    cV
    cW
    @0
    djhspss.h
    djhspss.u
    @1
    eqid
    #
    djhspss.v
    djhspss.n
    djhspss.k
    wph
    cX
    cY
    cV
    djhspss.x
    djhspss.y
    unssd
    dochspss
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cV
    wss
    cY
    cV
    wss
    @3
    @2
    wceq
    djhspss.k
    djhspss.x
    djhspss.y
    cU
    cH
    c.or
    cK
    @1
    cV
    cW
    cX
    cY
    djhspss.h
    djhspss.u
    djhspss.v
    @4
    djhspss.j
    djhval2
    syl3anc
    sseqtr4d
end
