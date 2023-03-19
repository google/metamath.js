include "cld.mm"
include "cfv.mm"
include "clfn.mm"
include "clspn.mm"
include "c0g.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "lcdvbaselfl.mm"
include "csn.mm"
include "wcel.mm"
include "wne.mm"
include "cdif.mm"
include "snssd.mm"
include "lcdlsp.mm"
include "eleqtrd.mm"
include "lcd0v2.mm"
include "neeqtrd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lkrlspeqN.mm"

theorem lcdlkreqN
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lcdlkreq.h: |- H = ( LHyp ` K )
  assume lcdlkreq.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdlkreq.l: |- L = ( LKer ` U )
  assume lcdlkreq.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlkreq.o: |- .0. = ( 0g ` C )
  assume lcdlkreq.n: |- N = ( LSpan ` C )
  assume lcdlkreq.v: |- V = ( Base ` C )
  assume lcdlkreq.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdlkreq.i: |- ( ph -> I e. V )
  assume lcdlkreq.g: |- ( ph -> G e. ( N ` { I } ) )
  assume lcdlkreq.z: |- ( ph -> G =/= .0. )


  assert |- ( ph -> ( L ` G ) = ( L ` I ) )

  proof
    wph
    cU
    cld
    cfv
    #
    cU
    clfn
    cfv
    #
    cG
    cI
    cL
    @0
    clspn
    cfv
    #
    cU
    @0
    c0g
    cfv
    #
    @1
    eqid
    #
    lcdlkreq.l
    @0
    eqid
    #
    @3
    eqid
    #
    @2
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    lcdlkreq.h
    lcdlkreq.u
    lcdlkreq.k
    dvhlvec
    wph
    cC
    cU
    @1
    cH
    cK
    cV
    cW
    cI
    lcdlkreq.h
    lcdlkreq.c
    lcdlkreq.v
    lcdlkreq.u
    @4
    lcdlkreq.k
    lcdlkreq.i
    lcdvbaselfl
    wph
    cG
    cI
    csn
    #
    @2
    cfv
    #
    wcel
    cG
    @3
    wne
    cG
    @9
    @3
    csn
    cdif
    wcel
    wph
    cG
    @8
    cN
    cfv
    @9
    lcdlkreq.g
    wph
    cC
    @0
    cU
    cV
    @8
    cH
    cK
    @2
    cN
    cW
    lcdlkreq.h
    lcdlkreq.u
    @5
    @7
    lcdlkreq.c
    lcdlkreq.v
    lcdlkreq.n
    lcdlkreq.k
    wph
    cI
    cV
    lcdlkreq.i
    snssd
    lcdlsp
    eleqtrd
    wph
    cG
    c.0
    @3
    lcdlkreq.z
    wph
    cC
    @0
    cU
    cH
    cK
    c.0
    cW
    @3
    lcdlkreq.h
    lcdlkreq.u
    @5
    @6
    lcdlkreq.c
    lcdlkreq.o
    lcdlkreq.k
    lcd0v2
    neeqtrd
    cG
    @9
    @3
    eldifsn
    sylanbrc
    lkrlspeqN
end
