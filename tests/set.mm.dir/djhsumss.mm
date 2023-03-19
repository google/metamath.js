include "co.mm"
include "cun.mm"
include "clspn.mm"
include "cfv.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsmssspx.mm"
include "djhspss.mm"
include "sstrd.mm"

theorem djhsumss
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhsumss.h: |- H = ( LHyp ` K )
  assume djhsumss.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhsumss.v: |- V = ( Base ` U )
  assume djhsumss.p: |- .(+) = ( LSSum ` U )
  assume djhsumss.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhsumss.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhsumss.x: |- ( ph -> X C_ V )
  assume djhsumss.y: |- ( ph -> Y C_ V )


  assert |- ( ph -> ( X .(+) Y ) C_ ( X .\/ Y ) )

  proof
    wph
    cX
    cY
    c.po
    co
    cX
    cY
    cun
    cU
    clspn
    cfv
    #
    cfv
    cX
    cY
    c.or
    co
    wph
    c.po
    cX
    cY
    @0
    cV
    cU
    djhsumss.v
    @0
    eqid
    #
    djhsumss.p
    djhsumss.x
    djhsumss.y
    wph
    cU
    cH
    cK
    cW
    djhsumss.h
    djhsumss.u
    djhsumss.k
    dvhlmod
    lsmssspx
    wph
    cU
    cH
    c.or
    cK
    @0
    cV
    cW
    cX
    cY
    djhsumss.h
    djhsumss.u
    djhsumss.v
    @1
    djhsumss.j
    djhsumss.k
    djhsumss.x
    djhsumss.y
    djhspss
    sstrd
end
