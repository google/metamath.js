include "cun.mm"
include "clspn.mm"
include "cfv.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "dvhlmod.mm"
include "unssd.mm"
include "eqid.mm"
include "lspssid.mm"
include "syl2anc.mm"
include "djhspss.mm"
include "sstrd.mm"

theorem djhunssN
  let wph: wff ph
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhunss.h: |- H = ( LHyp ` K )
  assume djhunss.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhunss.v: |- V = ( Base ` U )
  assume djhunss.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhunss.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhunss.x: |- ( ph -> X C_ V )
  assume djhunss.y: |- ( ph -> Y C_ V )


  assert |- ( ph -> ( X u. Y ) C_ ( X .\/ Y ) )

  proof
    wph
    cX
    cY
    cun
    #
    @0
    cU
    clspn
    cfv
    #
    cfv
    #
    cX
    cY
    c.or
    co
    wph
    cU
    clmod
    wcel
    @0
    cV
    wss
    @0
    @2
    wss
    wph
    cU
    cH
    cK
    cW
    djhunss.h
    djhunss.u
    djhunss.k
    dvhlmod
    wph
    cX
    cY
    cV
    djhunss.x
    djhunss.y
    unssd
    @0
    @1
    cV
    cU
    djhunss.v
    @1
    eqid
    #
    lspssid
    syl2anc
    wph
    cU
    cH
    c.or
    cK
    @1
    cV
    cW
    cX
    cY
    djhunss.h
    djhunss.u
    djhunss.v
    @3
    djhunss.j
    djhunss.k
    djhunss.x
    djhunss.y
    djhspss
    sstrd
end
