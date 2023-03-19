include "cv.mm"
include "co.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "c0g.mm"
include "csn.mm"
include "cbs.mm"
include "cltrn.mm"
include "eqid.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "snssd.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "lmodvacl.mm"
include "hdmapgln2.mm"
include "hdmapln1.mm"
include "cur.mm"
include "chvm.mm"
include "hdmapevec2.mm"
include "oveq2d.mm"
include "crg.mm"
include "wceq.mm"
include "lmodring.mm"
include "syl.mm"
include "ringridm.mm"
include "eqtrd.mm"
include "hdmapinvlem1.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grprid.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "hdmapinvlem2.mm"
include "ringrz.mm"
include "hdmapipcl.mm"
include "grplid.mm"

theorem hdmapglem7b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let c.po: class .(+)
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vk: setvar k
  let vl: setvar l
  let vu: setvar u
  let vv: setvar v
  let cY: class Y
  assume hdmapglem7.h: |- H = ( LHyp ` K )
  assume hdmapglem7.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapglem7.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapglem7.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglem7.v: |- V = ( Base ` U )
  assume hdmapglem7.p: |- .+ = ( +g ` U )
  assume hdmapglem7.q: |- .x. = ( .s ` U )
  assume hdmapglem7.r: |- R = ( Scalar ` U )
  assume hdmapglem7.b: |- B = ( Base ` R )
  assume hdmapglem7.a: |- .(+) = ( LSSum ` U )
  assume hdmapglem7.n: |- N = ( LSpan ` U )
  assume hdmapglem7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglem7.x: |- ( ph -> X e. V )
  assume hdmapglem7.t: |- .X. = ( .r ` R )
  assume hdmapglem7.z: |- .0. = ( 0g ` R )
  assume hdmapglem7.c: |- .+b = ( +g ` R )
  assume hdmapglem7.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapglem7.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapglem7b.u: |- ( ph -> x e. ( O ` { E } ) )
  assume hdmapglem7b.v: |- ( ph -> y e. ( O ` { E } ) )
  assume hdmapglem7b.k: |- ( ph -> m e. B )
  assume hdmapglem7b.l: |- ( ph -> n e. B )


  assert |- ( ph -> ( ( S ` ( ( m .x. E ) .+ x ) ) ` ( ( n .x. E ) .+ y ) ) = ( ( n .X. ( G ` m ) ) .+b ( ( S ` x ) ` y ) ) )

  proof
    wph
    vn
    cv
    #
    cE
    c.x
    co
    #
    vy
    cv
    #
    c.pl
    co
    #
    vm
    cv
    #
    cE
    c.x
    co
    vx
    cv
    #
    c.pl
    co
    cS
    cfv
    cfv
    @3
    cE
    cS
    cfv
    #
    cfv
    #
    @4
    cG
    cfv
    #
    c.xp
    co
    #
    @3
    @5
    cS
    cfv
    #
    cfv
    #
    c.pb
    co
    @0
    @8
    c.xp
    co
    #
    @2
    @10
    cfv
    #
    c.pb
    co
    wph
    @4
    cB
    c.pl
    c.pb
    cR
    cS
    c.x
    c.xp
    cU
    cG
    cH
    cK
    cV
    cW
    @3
    cE
    @5
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.c
    hdmapglem7.t
    hdmapglem7.s
    hdmapglem7.g
    hdmapglem7.k
    wph
    cU
    clmod
    wcel
    #
    @1
    cV
    wcel
    #
    @2
    cV
    wcel
    @3
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.k
    dvhlmod
    #
    wph
    @14
    @0
    cB
    wcel
    #
    cE
    cV
    wcel
    @15
    @16
    hdmapglem7b.l
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
    @18
    hdmapglem7.h
    @19
    eqid
    @20
    eqid
    hdmapglem7.u
    hdmapglem7.v
    @18
    eqid
    hdmapglem7.e
    hdmapglem7.k
    dvheveccl
    eldifad
    #
    @0
    c.x
    cR
    cB
    cV
    cU
    cE
    hdmapglem7.v
    hdmapglem7.r
    hdmapglem7.q
    hdmapglem7.b
    lmodvscl
    syl3anc
    wph
    cE
    csn
    #
    cO
    cfv
    #
    cV
    @2
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @22
    cV
    wss
    @23
    cV
    wss
    hdmapglem7.k
    wph
    cE
    cV
    @21
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @22
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.o
    dochssv
    syl2anc
    #
    hdmapglem7b.v
    sseldd
    #
    c.pl
    cV
    cU
    @1
    @2
    hdmapglem7.v
    hdmapglem7.p
    lmodvacl
    syl3anc
    @21
    wph
    @23
    cV
    @5
    @24
    hdmapglem7b.u
    sseldd
    #
    hdmapglem7b.k
    hdmapgln2
    wph
    @9
    @12
    @11
    @13
    c.pb
    wph
    @7
    @0
    @8
    c.xp
    wph
    @7
    @0
    cE
    @6
    cfv
    #
    c.xp
    co
    #
    @2
    @6
    cfv
    #
    c.pb
    co
    @0
    c.0
    c.pb
    co
    #
    @0
    wph
    @0
    cB
    c.pl
    c.pb
    cR
    cS
    c.x
    c.xp
    cU
    cH
    cK
    cV
    cW
    cE
    @2
    cE
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.c
    hdmapglem7.t
    hdmapglem7.s
    hdmapglem7.k
    @21
    @25
    @21
    hdmapglem7b.l
    hdmapln1
    wph
    @28
    @0
    @29
    c.0
    c.pb
    wph
    @28
    @0
    cR
    cur
    cfv
    #
    c.xp
    co
    #
    @0
    wph
    @27
    @31
    @0
    c.xp
    wph
    cR
    cS
    cU
    @31
    cE
    cH
    cW
    cK
    chvm
    cfv
    cfv
    #
    cK
    cW
    hdmapglem7.h
    hdmapglem7.e
    @33
    eqid
    hdmapglem7.s
    hdmapglem7.k
    hdmapglem7.u
    hdmapglem7.r
    @31
    eqid
    #
    hdmapevec2
    oveq2d
    wph
    cR
    crg
    wcel
    #
    @17
    @32
    @0
    wceq
    wph
    @14
    @35
    @16
    cR
    cU
    hdmapglem7.r
    lmodring
    syl
    #
    hdmapglem7b.l
    cB
    cR
    c.xp
    @31
    @0
    hdmapglem7.b
    hdmapglem7.t
    @34
    ringridm
    syl2anc
    eqtrd
    wph
    cB
    @2
    cR
    cS
    c.xp
    cU
    cE
    cH
    cK
    cO
    cV
    cW
    c.0
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.t
    hdmapglem7.z
    hdmapglem7.s
    hdmapglem7.k
    hdmapglem7b.v
    hdmapinvlem1
    oveq12d
    wph
    cR
    cgrp
    wcel
    #
    @17
    @30
    @0
    wceq
    wph
    @35
    @37
    @36
    cR
    ringgrp
    syl
    #
    hdmapglem7b.l
    cB
    c.pb
    cR
    @0
    c.0
    hdmapglem7.b
    hdmapglem7.c
    hdmapglem7.z
    grprid
    syl2anc
    3eqtrd
    oveq1d
    wph
    @11
    @0
    cE
    @10
    cfv
    #
    c.xp
    co
    #
    @13
    c.pb
    co
    c.0
    @13
    c.pb
    co
    #
    @13
    wph
    @0
    cB
    c.pl
    c.pb
    cR
    cS
    c.x
    c.xp
    cU
    cH
    cK
    cV
    cW
    cE
    @2
    @5
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.p
    hdmapglem7.q
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.c
    hdmapglem7.t
    hdmapglem7.s
    hdmapglem7.k
    @21
    @25
    @26
    hdmapglem7b.l
    hdmapln1
    wph
    @40
    c.0
    @13
    c.pb
    wph
    @40
    @0
    c.0
    c.xp
    co
    #
    c.0
    wph
    @39
    c.0
    @0
    c.xp
    wph
    cB
    @5
    cR
    cS
    c.xp
    cU
    cE
    cH
    cK
    cO
    cV
    cW
    c.0
    hdmapglem7.h
    hdmapglem7.e
    hdmapglem7.o
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.t
    hdmapglem7.z
    hdmapglem7.s
    hdmapglem7.k
    hdmapglem7b.u
    hdmapinvlem2
    oveq2d
    wph
    @35
    @17
    @42
    c.0
    wceq
    @36
    hdmapglem7b.l
    cB
    cR
    c.xp
    @0
    c.0
    hdmapglem7.b
    hdmapglem7.t
    hdmapglem7.z
    ringrz
    syl2anc
    eqtrd
    oveq1d
    wph
    @37
    @13
    cB
    wcel
    @41
    @13
    wceq
    @38
    wph
    cB
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @2
    @5
    hdmapglem7.h
    hdmapglem7.u
    hdmapglem7.v
    hdmapglem7.r
    hdmapglem7.b
    hdmapglem7.s
    hdmapglem7.k
    @25
    @26
    hdmapipcl
    cB
    c.pb
    cR
    @13
    c.0
    hdmapglem7.b
    hdmapglem7.c
    hdmapglem7.z
    grplid
    syl2anc
    3eqtrd
    oveq12d
    eqtrd
end
