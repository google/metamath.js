include "cfv.mm"
include "clk.mm"
include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "clfn.mm"
include "eqid.mm"
include "c0g.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "hdmaplkr.mm"
include "eleqtrrd.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "clcd.mm"
include "hdmapcl.mm"
include "lcdvbaselfl.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "snssd.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "ellkr2.mm"
include "mpbid.mm"

theorem hdmapinvlem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume hdmapinvlem1.h: |- H = ( LHyp ` K )
  assume hdmapinvlem1.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapinvlem1.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapinvlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapinvlem1.v: |- V = ( Base ` U )
  assume hdmapinvlem1.r: |- R = ( Scalar ` U )
  assume hdmapinvlem1.b: |- B = ( Base ` R )
  assume hdmapinvlem1.t: |- .x. = ( .r ` R )
  assume hdmapinvlem1.z: |- .0. = ( 0g ` R )
  assume hdmapinvlem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapinvlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapinvlem1.c: |- ( ph -> C e. ( O ` { E } ) )


  assert |- ( ph -> ( ( S ` E ) ` C ) = .0. )

  proof
    wph
    cC
    cE
    cS
    cfv
    #
    cU
    clk
    cfv
    #
    cfv
    #
    wcel
    cC
    @0
    cfv
    c.0
    wceq
    wph
    cC
    cE
    csn
    #
    cO
    cfv
    #
    @2
    hdmapinvlem1.c
    wph
    cS
    cU
    cU
    clfn
    cfv
    #
    cH
    cK
    cO
    cV
    cW
    cE
    @1
    hdmapinvlem1.h
    hdmapinvlem1.o
    hdmapinvlem1.u
    hdmapinvlem1.v
    @5
    eqid
    #
    @1
    eqid
    #
    hdmapinvlem1.s
    hdmapinvlem1.k
    wph
    cE
    cV
    cU
    c0g
    cfv
    #
    csn
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    cV
    cW
    @8
    hdmapinvlem1.h
    @9
    eqid
    @10
    eqid
    hdmapinvlem1.u
    hdmapinvlem1.v
    @8
    eqid
    hdmapinvlem1.e
    hdmapinvlem1.k
    dvheveccl
    eldifad
    #
    hdmaplkr
    eleqtrrd
    wph
    cR
    @5
    @0
    @1
    cV
    cU
    cC
    clmod
    c.0
    hdmapinvlem1.v
    hdmapinvlem1.r
    hdmapinvlem1.z
    @6
    @7
    wph
    cU
    cH
    cK
    cW
    hdmapinvlem1.h
    hdmapinvlem1.u
    hdmapinvlem1.k
    dvhlmod
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cU
    @5
    cH
    cK
    @12
    cbs
    cfv
    #
    cW
    @0
    hdmapinvlem1.h
    @12
    eqid
    #
    @13
    eqid
    #
    hdmapinvlem1.u
    @6
    hdmapinvlem1.k
    wph
    @12
    @13
    cS
    cE
    cU
    cH
    cK
    cV
    cW
    hdmapinvlem1.h
    hdmapinvlem1.u
    hdmapinvlem1.v
    @14
    @15
    hdmapinvlem1.s
    hdmapinvlem1.k
    @11
    hdmapcl
    lcdvbaselfl
    wph
    @4
    cV
    cC
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    cV
    wss
    @4
    cV
    wss
    hdmapinvlem1.k
    wph
    cE
    cV
    @11
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @3
    hdmapinvlem1.h
    hdmapinvlem1.u
    hdmapinvlem1.v
    hdmapinvlem1.o
    dochssv
    syl2anc
    hdmapinvlem1.c
    sseldd
    ellkr2
    mpbid
end
