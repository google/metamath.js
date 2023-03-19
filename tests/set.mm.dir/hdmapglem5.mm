include "cur.mm"
include "cfv.mm"
include "co.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodring.mm"
include "syl.mm"
include "csn.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "c0g.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "hdmapipcl.mm"
include "hgmapcl.mm"
include "ringlidm.mm"
include "ringidcl.mm"
include "hgmapval1.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "eqtrd.mm"
include "hdmapinvlem4.mm"
include "eqtr3d.mm"

theorem hdmapglem5
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.mi: class .-
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume hdmapglem5.h: |- H = ( LHyp ` K )
  assume hdmapglem5.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapglem5.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapglem5.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglem5.v: |- V = ( Base ` U )
  assume hdmapglem5.p: |- .+ = ( +g ` U )
  assume hdmapglem5.m: |- .- = ( -g ` U )
  assume hdmapglem5.q: |- .x. = ( .s ` U )
  assume hdmapglem5.r: |- R = ( Scalar ` U )
  assume hdmapglem5.b: |- B = ( Base ` R )
  assume hdmapglem5.t: |- .X. = ( .r ` R )
  assume hdmapglem5.z: |- .0. = ( 0g ` R )
  assume hdmapglem5.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapglem5.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapglem5.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglem5.c: |- ( ph -> C e. ( O ` { E } ) )
  assume hdmapglem5.d: |- ( ph -> D e. ( O ` { E } ) )
  assume hdmapglem5.i: |- ( ph -> I e. B )
  assume hdmapglem5.j: |- ( ph -> J e. B )


  assert |- ( ph -> ( G ` ( ( S ` D ) ` C ) ) = ( ( S ` C ) ` D ) )

  proof
    wph
    cR
    cur
    cfv
    #
    cC
    cD
    cS
    cfv
    cfv
    #
    cG
    cfv
    #
    c.xp
    co
    #
    @2
    cD
    cC
    cS
    cfv
    cfv
    wph
    cR
    crg
    wcel
    #
    @2
    cB
    wcel
    @3
    @2
    wceq
    wph
    cU
    clmod
    wcel
    @4
    wph
    cU
    cH
    cK
    cW
    hdmapglem5.h
    hdmapglem5.u
    hdmapglem5.k
    dvhlmod
    cR
    cU
    hdmapglem5.r
    lmodring
    syl
    #
    wph
    cB
    cR
    cU
    @1
    cG
    cH
    cK
    cW
    hdmapglem5.h
    hdmapglem5.u
    hdmapglem5.r
    hdmapglem5.b
    hdmapglem5.g
    hdmapglem5.k
    wph
    cB
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cC
    cD
    hdmapglem5.h
    hdmapglem5.u
    hdmapglem5.v
    hdmapglem5.r
    hdmapglem5.b
    hdmapglem5.s
    hdmapglem5.k
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
    @6
    cV
    wss
    @7
    cV
    wss
    hdmapglem5.k
    wph
    cE
    cV
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
    hdmapglem5.h
    @9
    eqid
    @10
    eqid
    hdmapglem5.u
    hdmapglem5.v
    @8
    eqid
    hdmapglem5.e
    hdmapglem5.k
    dvheveccl
    eldifad
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @6
    hdmapglem5.h
    hdmapglem5.u
    hdmapglem5.v
    hdmapglem5.o
    dochssv
    syl2anc
    #
    hdmapglem5.c
    sseldd
    wph
    @7
    cV
    cD
    @11
    hdmapglem5.d
    sseldd
    hdmapipcl
    #
    hgmapcl
    cB
    cR
    c.xp
    @0
    @2
    hdmapglem5.b
    hdmapglem5.t
    @0
    eqid
    #
    ringlidm
    syl2anc
    wph
    cB
    cC
    cD
    c.pl
    cR
    cS
    c.x
    c.xp
    cU
    cE
    cG
    cH
    @1
    @0
    cK
    c.mi
    cO
    cV
    cW
    c.0
    hdmapglem5.h
    hdmapglem5.e
    hdmapglem5.o
    hdmapglem5.u
    hdmapglem5.v
    hdmapglem5.p
    hdmapglem5.m
    hdmapglem5.q
    hdmapglem5.r
    hdmapglem5.b
    hdmapglem5.t
    hdmapglem5.z
    hdmapglem5.s
    hdmapglem5.g
    hdmapglem5.k
    hdmapglem5.c
    hdmapglem5.d
    @12
    wph
    @4
    @0
    cB
    wcel
    @5
    cB
    cR
    @0
    hdmapglem5.b
    @13
    ringidcl
    syl
    wph
    @1
    @0
    cG
    cfv
    #
    c.xp
    co
    @1
    @0
    c.xp
    co
    #
    @1
    wph
    @14
    @0
    @1
    c.xp
    wph
    cR
    cU
    @0
    cG
    cH
    cK
    cW
    hdmapglem5.h
    hdmapglem5.u
    hdmapglem5.r
    @13
    hdmapglem5.g
    hdmapglem5.k
    hgmapval1
    oveq2d
    wph
    @4
    @1
    cB
    wcel
    @15
    @1
    wceq
    @5
    @12
    cB
    cR
    c.xp
    @0
    @1
    hdmapglem5.b
    hdmapglem5.t
    @13
    ringridm
    syl2anc
    eqtrd
    hdmapinvlem4
    eqtr3d
end
