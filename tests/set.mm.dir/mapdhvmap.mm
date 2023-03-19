include "csn.mm"
include "cfv.mm"
include "cld.mm"
include "clspn.mm"
include "clfn.mm"
include "clk.mm"
include "coch.mm"
include "eqid.mm"
include "eldifad.mm"
include "hvmaplfl.mm"
include "hvmaplkr.mm"
include "mapdsn3.mm"
include "cbs.mm"
include "c0g.mm"
include "hvmapcl2.mm"
include "snssd.mm"
include "lcdlsp.mm"
include "eqtr4d.mm"

theorem mapdhvmap
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cU: class U
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume mapdhvmap.h: |- H = ( LHyp ` K )
  assume mapdhvmap.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdhvmap.v: |- V = ( Base ` U )
  assume mapdhvmap.z: |- .0. = ( 0g ` U )
  assume mapdhvmap.n: |- N = ( LSpan ` U )
  assume mapdhvmap.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdhvmap.j: |- J = ( LSpan ` C )
  assume mapdhvmap.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdhvmap.p: |- P = ( ( HVMap ` K ) ` W )
  assume mapdhvmap.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhvmap.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { ( P ` X ) } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    cM
    cfv
    cX
    cP
    cfv
    #
    csn
    #
    cU
    cld
    cfv
    #
    clspn
    cfv
    #
    cfv
    @1
    cJ
    cfv
    wph
    @2
    @3
    cU
    cU
    clfn
    cfv
    #
    @0
    cH
    cK
    cU
    clk
    cfv
    #
    cM
    cN
    cW
    cK
    coch
    cfv
    cfv
    #
    cV
    cW
    cX
    mapdhvmap.h
    @6
    eqid
    #
    mapdhvmap.m
    mapdhvmap.u
    mapdhvmap.v
    mapdhvmap.n
    @4
    eqid
    #
    @5
    eqid
    #
    @2
    eqid
    #
    @3
    eqid
    #
    mapdhvmap.k
    wph
    cX
    cV
    c.0
    csn
    mapdhvmap.x
    eldifad
    wph
    cU
    @4
    cH
    cK
    cP
    cV
    cW
    cX
    c.0
    mapdhvmap.h
    mapdhvmap.u
    mapdhvmap.v
    mapdhvmap.z
    @8
    mapdhvmap.p
    mapdhvmap.k
    mapdhvmap.x
    hvmaplfl
    wph
    cU
    cH
    cK
    @5
    cP
    @6
    cV
    cW
    cX
    c.0
    mapdhvmap.h
    @7
    mapdhvmap.u
    mapdhvmap.v
    mapdhvmap.z
    @9
    mapdhvmap.p
    mapdhvmap.k
    mapdhvmap.x
    hvmaplkr
    mapdsn3
    wph
    cC
    @2
    cU
    cC
    cbs
    cfv
    #
    @1
    cH
    cK
    @3
    cJ
    cW
    mapdhvmap.h
    mapdhvmap.u
    @10
    @11
    mapdhvmap.c
    @12
    eqid
    #
    mapdhvmap.j
    mapdhvmap.k
    wph
    @0
    @12
    wph
    @0
    @12
    cC
    c0g
    cfv
    #
    csn
    wph
    cC
    cU
    @12
    cH
    cK
    cP
    @14
    cV
    cW
    cX
    c.0
    mapdhvmap.h
    mapdhvmap.u
    mapdhvmap.v
    mapdhvmap.z
    mapdhvmap.c
    @13
    @14
    eqid
    mapdhvmap.p
    mapdhvmap.k
    mapdhvmap.x
    hvmapcl2
    eldifad
    snssd
    lcdlsp
    eqtr4d
end
