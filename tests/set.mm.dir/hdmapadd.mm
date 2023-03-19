include "cbs.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "chdma1.mm"
include "chvm.mm"
include "clspn.mm"
include "cmpd.mm"
include "c0g.mm"
include "eqid.mm"
include "hdmap11lem2.mm"

theorem hdmapadd
  let wph: wff ph
  let cC: class C
  let c.pl: class .+
  let c.pb: class .+b
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume hdmap11.h: |- H = ( LHyp ` K )
  assume hdmap11.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap11.v: |- V = ( Base ` U )
  assume hdmap11.p: |- .+ = ( +g ` U )
  assume hdmap11.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap11.a: |- .+b = ( +g ` C )
  assume hdmap11.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap11.x: |- ( ph -> X e. V )
  assume hdmap11.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( S ` ( X .+ Y ) ) = ( ( S ` X ) .+b ( S ` Y ) ) )

  proof
    wph
    cC
    cC
    cbs
    cfv
    #
    c.pl
    c.pb
    cS
    cU
    cid
    cK
    cbs
    cfv
    cres
    cid
    cW
    cK
    cltrn
    cfv
    cfv
    cres
    cop
    #
    cH
    cW
    cK
    chdma1
    cfv
    cfv
    #
    cW
    cK
    chvm
    cfv
    cfv
    #
    cK
    cC
    clspn
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    cU
    clspn
    cfv
    #
    cV
    cW
    cX
    cY
    cU
    c0g
    cfv
    #
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.p
    hdmap11.c
    hdmap11.a
    hdmap11.s
    hdmap11.k
    hdmap11.x
    hdmap11.y
    @1
    eqid
    @7
    eqid
    @6
    eqid
    @0
    eqid
    @4
    eqid
    @5
    eqid
    @3
    eqid
    @2
    eqid
    hdmap11lem2
end
