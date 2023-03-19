include "clcd.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "c0g.mm"
include "csn.mm"
include "hvmapcl2.mm"
include "eldifad.mm"
include "lcdvbaselfl.mm"

theorem hvmaplfl
  let wph: wff ph
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume hvmaplfl.h: |- H = ( LHyp ` K )
  assume hvmaplfl.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmaplfl.v: |- V = ( Base ` U )
  assume hvmaplfl.z: |- .0. = ( 0g ` U )
  assume hvmaplfl.f: |- F = ( LFnl ` U )
  assume hvmaplfl.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmaplfl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hvmaplfl.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( M ` X ) e. F )

  proof
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cU
    cF
    cH
    cK
    @0
    cbs
    cfv
    #
    cW
    cX
    cM
    cfv
    #
    hvmaplfl.h
    @0
    eqid
    #
    @1
    eqid
    #
    hvmaplfl.u
    hvmaplfl.f
    hvmaplfl.k
    wph
    @2
    @1
    @0
    c0g
    cfv
    #
    csn
    wph
    @0
    cU
    @1
    cH
    cK
    cM
    @5
    cV
    cW
    cX
    c.0
    hvmaplfl.h
    hvmaplfl.u
    hvmaplfl.v
    hvmaplfl.z
    @3
    @4
    @5
    eqid
    hvmaplfl.m
    hvmaplfl.k
    hvmaplfl.x
    hvmapcl2
    eldifad
    lcdvbaselfl
end
