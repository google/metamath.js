include "co.mm"
include "cfv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodvnegcl.mm"
include "hdmapadd.mm"
include "hdmapneg.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cbs.mm"
include "hdmapcl.mm"
include "eqtr4d.mm"

theorem hdmapsub
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume hdmap12c.h: |- H = ( LHyp ` K )
  assume hdmap12c.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap12c.v: |- V = ( Base ` U )
  assume hdmap12c.m: |- .- = ( -g ` U )
  assume hdmap12c.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap12c.n: |- N = ( -g ` C )
  assume hdmap12c.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap12c.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap12c.x: |- ( ph -> X e. V )
  assume hdmap12c.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( S ` ( X .- Y ) ) = ( ( S ` X ) N ( S ` Y ) ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    cS
    cfv
    #
    cX
    cS
    cfv
    #
    cY
    cS
    cfv
    #
    cC
    cminusg
    cfv
    #
    cfv
    #
    cC
    cplusg
    cfv
    #
    co
    #
    @2
    @3
    cN
    co
    #
    wph
    @1
    cX
    cY
    cU
    cminusg
    cfv
    #
    cfv
    #
    cU
    cplusg
    cfv
    #
    co
    #
    cS
    cfv
    @2
    @10
    cS
    cfv
    #
    @6
    co
    @7
    wph
    @0
    @12
    cS
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    #
    @0
    @12
    wceq
    hdmap12c.x
    hdmap12c.y
    cV
    @11
    cU
    @9
    c.mi
    cX
    cY
    hdmap12c.v
    @11
    eqid
    #
    @9
    eqid
    #
    hdmap12c.m
    grpsubval
    syl2anc
    fveq2d
    wph
    cC
    @11
    @6
    cS
    cU
    cH
    cK
    cV
    cW
    cX
    @10
    hdmap12c.h
    hdmap12c.u
    hdmap12c.v
    @15
    hdmap12c.c
    @6
    eqid
    #
    hdmap12c.s
    hdmap12c.k
    hdmap12c.x
    wph
    cU
    clmod
    wcel
    @14
    @10
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap12c.h
    hdmap12c.u
    hdmap12c.k
    dvhlmod
    hdmap12c.y
    @9
    cV
    cU
    cY
    hdmap12c.v
    @16
    lmodvnegcl
    syl2anc
    hdmapadd
    wph
    @13
    @5
    @2
    @6
    wph
    cC
    cS
    cY
    cU
    cH
    @4
    cK
    @9
    cV
    cW
    hdmap12c.h
    hdmap12c.u
    hdmap12c.v
    @16
    hdmap12c.c
    @4
    eqid
    #
    hdmap12c.s
    hdmap12c.k
    hdmap12c.y
    hdmapneg
    oveq2d
    3eqtrd
    wph
    @2
    cC
    cbs
    cfv
    #
    wcel
    @3
    @19
    wcel
    @8
    @7
    wceq
    wph
    cC
    @19
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmap12c.h
    hdmap12c.u
    hdmap12c.v
    hdmap12c.c
    @19
    eqid
    #
    hdmap12c.s
    hdmap12c.k
    hdmap12c.x
    hdmapcl
    wph
    cC
    @19
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    hdmap12c.h
    hdmap12c.u
    hdmap12c.v
    hdmap12c.c
    @20
    hdmap12c.s
    hdmap12c.k
    hdmap12c.y
    hdmapcl
    @19
    @6
    cC
    @4
    cN
    @2
    @3
    @20
    @17
    @18
    hdmap12c.n
    grpsubval
    syl2anc
    eqtr4d
end
