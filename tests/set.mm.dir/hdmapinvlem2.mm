include "cfv.mm"
include "wceq.mm"
include "hdmapinvlem1.mm"
include "c0g.mm"
include "csn.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "snssd.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "hdmapip0com.mm"
include "mpbid.mm"

theorem hdmapinvlem2
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


  assert |- ( ph -> ( ( S ` C ) ` E ) = .0. )

  proof
    wph
    cC
    cE
    cS
    cfv
    cfv
    c.0
    wceq
    cE
    cC
    cS
    cfv
    cfv
    c.0
    wceq
    wph
    cB
    cC
    cR
    cS
    c.x
    cU
    cE
    cH
    cK
    cO
    cV
    cW
    c.0
    hdmapinvlem1.h
    hdmapinvlem1.e
    hdmapinvlem1.o
    hdmapinvlem1.u
    hdmapinvlem1.v
    hdmapinvlem1.r
    hdmapinvlem1.b
    hdmapinvlem1.t
    hdmapinvlem1.z
    hdmapinvlem1.s
    hdmapinvlem1.k
    hdmapinvlem1.c
    hdmapinvlem1
    wph
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cE
    cC
    c.0
    hdmapinvlem1.h
    hdmapinvlem1.u
    hdmapinvlem1.v
    hdmapinvlem1.r
    hdmapinvlem1.z
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
    @0
    hdmapinvlem1.h
    @1
    eqid
    @2
    eqid
    hdmapinvlem1.u
    hdmapinvlem1.v
    @0
    eqid
    hdmapinvlem1.e
    hdmapinvlem1.k
    dvheveccl
    eldifad
    #
    wph
    cE
    csn
    #
    cO
    cfv
    #
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
    @4
    cV
    wss
    @5
    cV
    wss
    hdmapinvlem1.k
    wph
    cE
    cV
    @3
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @4
    hdmapinvlem1.h
    hdmapinvlem1.u
    hdmapinvlem1.v
    hdmapinvlem1.o
    dochssv
    syl2anc
    hdmapinvlem1.c
    sseldd
    hdmapip0com
    mpbid
end
