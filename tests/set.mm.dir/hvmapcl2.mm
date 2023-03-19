include "csn.mm"
include "cdif.mm"
include "wf1o.mm"
include "wf.mm"
include "hvmap1o2.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnd.mm"

theorem hvmapcl2
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  assume hvmap1o2.h: |- H = ( LHyp ` K )
  assume hvmap1o2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmap1o2.v: |- V = ( Base ` U )
  assume hvmap1o2.z: |- .0. = ( 0g ` U )
  assume hvmap1o2.c: |- C = ( ( LCDual ` K ) ` W )
  assume hvmap1o2.f: |- F = ( Base ` C )
  assume hvmap1o2.o: |- O = ( 0g ` C )
  assume hvmap1o2.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmap1o2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hvmapcl2.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( M ` X ) e. ( F \ { O } ) )

  proof
    wph
    cV
    c.0
    csn
    cdif
    #
    cF
    cO
    csn
    cdif
    #
    cX
    cM
    wph
    @0
    @1
    cM
    wf1o
    @0
    @1
    cM
    wf
    wph
    cC
    cU
    cF
    cH
    cK
    cM
    cO
    cV
    cW
    c.0
    hvmap1o2.h
    hvmap1o2.u
    hvmap1o2.v
    hvmap1o2.z
    hvmap1o2.c
    hvmap1o2.f
    hvmap1o2.o
    hvmap1o2.m
    hvmap1o2.k
    hvmap1o2
    @0
    @1
    cM
    f1of
    syl
    hvmapcl2.x
    ffvelrnd
end
