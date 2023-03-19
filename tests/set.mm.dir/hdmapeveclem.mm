include "cfv.mm"
include "cotp.mm"
include "c0g.mm"
include "csn.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "hdmapval2.mm"
include "clspn.mm"
include "cmpd.mm"
include "hvmapcl2.mm"
include "mapdhvmap.mm"
include "dvhlmod.mm"
include "hdmaplem1.mm"
include "necomd.mm"
include "hdmaplem3.mm"
include "eqidd.mm"
include "hdmap1eq2.mm"
include "eqtrd.mm"

theorem hdmapeveclem
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume hdmapevec.h: |- H = ( LHyp ` K )
  assume hdmapevec.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapevec.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapevec.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapevec.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapevec.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapevec.v: |- V = ( Base ` U )
  assume hdmapevec.n: |- N = ( LSpan ` U )
  assume hdmapevec.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapevec.d: |- D = ( Base ` C )
  assume hdmapevec.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapevec.x: |- ( ph -> X e. V )
  assume hdmapevec.ne: |- ( ph -> -. X e. ( ( N ` { E } ) u. ( N ` { E } ) ) )


  assert |- ( ph -> ( S ` E ) = ( J ` E ) )

  proof
    wph
    cE
    cS
    cfv
    cX
    cE
    cE
    cJ
    cfv
    #
    cX
    cotp
    cI
    cfv
    #
    cE
    cotp
    cI
    cfv
    @0
    wph
    cC
    cD
    cS
    cE
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    cX
    hdmapevec.h
    hdmapevec.e
    hdmapevec.u
    hdmapevec.v
    hdmapevec.n
    hdmapevec.c
    hdmapevec.d
    hdmapevec.j
    hdmapevec.i
    hdmapevec.s
    hdmapevec.k
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
    @2
    hdmapevec.h
    @3
    eqid
    @4
    eqid
    hdmapevec.u
    hdmapevec.v
    @2
    eqid
    #
    hdmapevec.e
    hdmapevec.k
    dvheveccl
    #
    eldifad
    #
    hdmapevec.x
    hdmapevec.ne
    hdmapval2
    wph
    cC
    cD
    cU
    @0
    @1
    cH
    cI
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
    cN
    cV
    cW
    cE
    cX
    @2
    hdmapevec.h
    hdmapevec.u
    hdmapevec.v
    @5
    hdmapevec.n
    hdmapevec.c
    hdmapevec.d
    @8
    eqid
    #
    @9
    eqid
    #
    hdmapevec.i
    hdmapevec.k
    wph
    @0
    cD
    cC
    c0g
    cfv
    #
    csn
    wph
    cC
    cU
    cD
    cH
    cK
    cJ
    @12
    cV
    cW
    cE
    @2
    hdmapevec.h
    hdmapevec.u
    hdmapevec.v
    @5
    hdmapevec.c
    hdmapevec.d
    @12
    eqid
    hdmapevec.j
    hdmapevec.k
    @6
    hvmapcl2
    eldifad
    wph
    cC
    cJ
    cU
    cH
    @8
    cK
    @9
    cN
    cV
    cW
    cE
    @2
    hdmapevec.h
    hdmapevec.u
    hdmapevec.v
    @5
    hdmapevec.n
    hdmapevec.c
    @10
    @11
    hdmapevec.j
    hdmapevec.k
    @6
    mapdhvmap
    wph
    cX
    csn
    cN
    cfv
    cE
    csn
    cN
    cfv
    wph
    cN
    cV
    cU
    cE
    cE
    cX
    hdmapevec.v
    hdmapevec.n
    wph
    cU
    cH
    cK
    cW
    hdmapevec.h
    hdmapevec.u
    hdmapevec.k
    dvhlmod
    #
    hdmapevec.x
    hdmapevec.ne
    @7
    hdmaplem1
    necomd
    @6
    wph
    cN
    cV
    cU
    cE
    cE
    @2
    cX
    hdmapevec.v
    hdmapevec.n
    @13
    hdmapevec.x
    hdmapevec.ne
    @7
    @5
    hdmaplem3
    wph
    @1
    eqidd
    hdmap1eq2
    eqtrd
end
