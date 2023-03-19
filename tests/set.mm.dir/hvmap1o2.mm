include "csn.mm"
include "cdif.mm"
include "wf1o.mm"
include "cv.mm"
include "clk.mm"
include "cfv.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cld.mm"
include "c0g.mm"
include "eqid.mm"
include "hvmap1o.mm"
include "wb.mm"
include "lcdvbase.mm"
include "lcd0v2.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "f1oeq3.mm"
include "syl.mm"
include "mpbird.mm"

theorem hvmap1o2
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


  assert |- ( ph -> M : ( V \ { .0. } ) -1-1-onto-> ( F \ { O } ) )

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
    #
    cdif
    #
    cM
    wf1o
    #
    @0
    vf
    cv
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    @6
    cfv
    @5
    wceq
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cU
    cld
    cfv
    #
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    cM
    wf1o
    #
    wph
    @8
    @9
    @10
    cU
    vf
    @7
    cH
    cK
    @4
    cM
    @6
    cV
    cW
    c.0
    hvmap1o2.h
    @6
    eqid
    #
    hvmap1o2.u
    hvmap1o2.v
    hvmap1o2.z
    @7
    eqid
    #
    @4
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    @8
    eqid
    #
    hvmap1o2.m
    hvmap1o2.k
    hvmap1o
    wph
    @2
    @12
    wceq
    @3
    @13
    wb
    wph
    cF
    @8
    @1
    @11
    wph
    @8
    cC
    cU
    vf
    @7
    cH
    cK
    @4
    @6
    cF
    cW
    hvmap1o2.h
    @14
    hvmap1o2.c
    hvmap1o2.f
    hvmap1o2.u
    @15
    @16
    @19
    hvmap1o2.k
    lcdvbase
    wph
    cO
    @10
    wph
    cC
    @9
    cU
    cH
    cK
    cO
    cW
    @10
    hvmap1o2.h
    hvmap1o2.u
    @17
    @18
    hvmap1o2.c
    hvmap1o2.o
    hvmap1o2.k
    lcd0v2
    sneqd
    difeq12d
    @2
    @12
    @0
    cM
    f1oeq3
    syl
    mpbird
end
