include "co.mm"
include "cfv.mm"
include "clcd.mm"
include "csg.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "c0g.mm"
include "csn.mm"
include "cbs.mm"
include "cltrn.mm"
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
include "hdmapsub.mm"
include "fveq1d.mm"
include "hdmapcl.mm"
include "lmodvacl.mm"
include "lcdvsubval.mm"
include "cplusg.mm"
include "hdmaplna1.mm"
include "hdmapglnm2.mm"
include "cur.mm"
include "hdmaplnm1.mm"
include "chvm.mm"
include "hdmapevec2.mm"
include "oveq2d.mm"
include "crg.mm"
include "wceq.mm"
include "lmodring.mm"
include "syl.mm"
include "ringridm.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "hdmapinvlem1.mm"
include "hgmapcl.mm"
include "ringlz.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "lmodmcl.mm"
include "grprid.mm"
include "hdmapinvlem2.mm"
include "ringrz.mm"
include "3eqtrrd.mm"
include "grplid.mm"
include "3eqtr2d.mm"
include "grpsubid.mm"

theorem hdmapinvlem3
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
  assume hdmapinvlem3.h: |- H = ( LHyp ` K )
  assume hdmapinvlem3.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapinvlem3.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapinvlem3.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapinvlem3.v: |- V = ( Base ` U )
  assume hdmapinvlem3.p: |- .+ = ( +g ` U )
  assume hdmapinvlem3.m: |- .- = ( -g ` U )
  assume hdmapinvlem3.q: |- .x. = ( .s ` U )
  assume hdmapinvlem3.r: |- R = ( Scalar ` U )
  assume hdmapinvlem3.b: |- B = ( Base ` R )
  assume hdmapinvlem3.t: |- .X. = ( .r ` R )
  assume hdmapinvlem3.z: |- .0. = ( 0g ` R )
  assume hdmapinvlem3.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapinvlem3.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapinvlem3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapinvlem3.c: |- ( ph -> C e. ( O ` { E } ) )
  assume hdmapinvlem3.d: |- ( ph -> D e. ( O ` { E } ) )
  assume hdmapinvlem3.i: |- ( ph -> I e. B )
  assume hdmapinvlem3.j: |- ( ph -> J e. B )
  assume hdmapinvlem3.ij: |- ( ph -> ( I .X. ( G ` J ) ) = ( ( S ` D ) ` C ) )


  assert |- ( ph -> ( ( S ` ( ( J .x. E ) .- D ) ) ` ( ( I .x. E ) .+ C ) ) = .0. )

  proof
    wph
    cI
    cE
    c.x
    co
    #
    cC
    c.pl
    co
    #
    cJ
    cE
    c.x
    co
    #
    cD
    c.mi
    co
    cS
    cfv
    #
    cfv
    @1
    @2
    cS
    cfv
    #
    cD
    cS
    cfv
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    csg
    cfv
    #
    co
    #
    cfv
    #
    cI
    cJ
    cG
    cfv
    #
    c.xp
    co
    #
    @11
    cR
    csg
    cfv
    #
    co
    #
    c.0
    wph
    @1
    @3
    @8
    wph
    @6
    cS
    cU
    cH
    cK
    c.mi
    @7
    cV
    cW
    @2
    cD
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.m
    @6
    eqid
    #
    @7
    eqid
    #
    hdmapinvlem3.s
    hdmapinvlem3.k
    wph
    cU
    clmod
    wcel
    #
    cJ
    cB
    wcel
    cE
    cV
    wcel
    #
    @2
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.k
    dvhlmod
    #
    hdmapinvlem3.j
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
    @19
    hdmapinvlem3.h
    @20
    eqid
    @21
    eqid
    hdmapinvlem3.u
    hdmapinvlem3.v
    @19
    eqid
    hdmapinvlem3.e
    hdmapinvlem3.k
    dvheveccl
    eldifad
    #
    cJ
    c.x
    cR
    cB
    cV
    cU
    cE
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.q
    hdmapinvlem3.b
    lmodvscl
    syl3anc
    #
    wph
    cE
    csn
    #
    cO
    cfv
    #
    cV
    cD
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @24
    cV
    wss
    @25
    cV
    wss
    hdmapinvlem3.k
    wph
    cE
    cV
    @22
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @24
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.o
    dochssv
    syl2anc
    #
    hdmapinvlem3.d
    sseldd
    #
    hdmapsub
    fveq1d
    wph
    @9
    @1
    @4
    cfv
    #
    @1
    @5
    cfv
    #
    @12
    co
    @13
    wph
    @6
    @6
    cbs
    cfv
    #
    cR
    @12
    cU
    @4
    @5
    cH
    cK
    @7
    cV
    cW
    @1
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.r
    @12
    eqid
    #
    @14
    @30
    eqid
    #
    @15
    hdmapinvlem3.k
    wph
    @6
    @30
    cS
    @2
    cU
    cH
    cK
    cV
    cW
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    @14
    @32
    hdmapinvlem3.s
    hdmapinvlem3.k
    @23
    hdmapcl
    wph
    @6
    @30
    cS
    cD
    cU
    cH
    cK
    cV
    cW
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    @14
    @32
    hdmapinvlem3.s
    hdmapinvlem3.k
    @27
    hdmapcl
    wph
    @16
    @0
    cV
    wcel
    #
    cC
    cV
    wcel
    @1
    cV
    wcel
    @18
    wph
    @16
    cI
    cB
    wcel
    #
    @17
    @33
    @18
    hdmapinvlem3.i
    @22
    cI
    c.x
    cR
    cB
    cV
    cU
    cE
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.q
    hdmapinvlem3.b
    lmodvscl
    syl3anc
    #
    wph
    @25
    cV
    cC
    @26
    hdmapinvlem3.c
    sseldd
    #
    c.pl
    cV
    cU
    @0
    cC
    hdmapinvlem3.v
    hdmapinvlem3.p
    lmodvacl
    syl3anc
    lcdvsubval
    wph
    @28
    @11
    @29
    @11
    @12
    wph
    @28
    @0
    @4
    cfv
    #
    cC
    @4
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    @11
    c.0
    @39
    co
    #
    @11
    wph
    c.pl
    @39
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @0
    cC
    @2
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.p
    hdmapinvlem3.r
    @39
    eqid
    #
    hdmapinvlem3.s
    hdmapinvlem3.k
    @35
    @36
    @23
    hdmaplna1
    wph
    @37
    @11
    @38
    c.0
    @39
    wph
    @37
    @0
    cE
    cS
    cfv
    #
    cfv
    #
    @10
    c.xp
    co
    @11
    wph
    cJ
    cB
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
    @0
    cE
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.q
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.s
    hdmapinvlem3.g
    hdmapinvlem3.k
    @35
    @22
    hdmapinvlem3.j
    hdmapglnm2
    wph
    @43
    cI
    @10
    c.xp
    wph
    @43
    cI
    cE
    @42
    cfv
    #
    c.xp
    co
    cI
    cR
    cur
    cfv
    #
    c.xp
    co
    #
    cI
    wph
    cI
    cB
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
    cE
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.q
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.s
    hdmapinvlem3.k
    @22
    @22
    hdmapinvlem3.i
    hdmaplnm1
    wph
    @44
    @45
    cI
    c.xp
    wph
    cR
    cS
    cU
    @45
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
    hdmapinvlem3.h
    hdmapinvlem3.e
    @47
    eqid
    hdmapinvlem3.s
    hdmapinvlem3.k
    hdmapinvlem3.u
    hdmapinvlem3.r
    @45
    eqid
    #
    hdmapevec2
    oveq2d
    wph
    cR
    crg
    wcel
    #
    @34
    @46
    cI
    wceq
    wph
    @16
    @49
    @18
    cR
    cU
    hdmapinvlem3.r
    lmodring
    syl
    #
    hdmapinvlem3.i
    cB
    cR
    c.xp
    @45
    cI
    hdmapinvlem3.b
    hdmapinvlem3.t
    @48
    ringridm
    syl2anc
    3eqtrd
    oveq1d
    eqtrd
    wph
    @38
    cC
    @42
    cfv
    #
    @10
    c.xp
    co
    c.0
    @10
    c.xp
    co
    #
    c.0
    wph
    cJ
    cB
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
    cC
    cE
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.q
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.s
    hdmapinvlem3.g
    hdmapinvlem3.k
    @36
    @22
    hdmapinvlem3.j
    hdmapglnm2
    wph
    @51
    c.0
    @10
    c.xp
    wph
    cB
    cC
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
    hdmapinvlem3.h
    hdmapinvlem3.e
    hdmapinvlem3.o
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.z
    hdmapinvlem3.s
    hdmapinvlem3.k
    hdmapinvlem3.c
    hdmapinvlem1
    oveq1d
    wph
    @49
    @10
    cB
    wcel
    #
    @52
    c.0
    wceq
    @50
    wph
    cB
    cR
    cU
    cJ
    cG
    cH
    cK
    cW
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.g
    hdmapinvlem3.k
    hdmapinvlem3.j
    hgmapcl
    #
    cB
    cR
    c.xp
    @10
    c.0
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.z
    ringlz
    syl2anc
    3eqtrd
    oveq12d
    wph
    cR
    cgrp
    wcel
    #
    @11
    cB
    wcel
    #
    @40
    @11
    wceq
    wph
    @49
    @55
    @50
    cR
    ringgrp
    syl
    #
    wph
    @16
    @34
    @53
    @56
    @18
    hdmapinvlem3.i
    @54
    c.xp
    cR
    cB
    cU
    cI
    @10
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    lmodmcl
    syl3anc
    #
    cB
    @39
    cR
    @11
    c.0
    hdmapinvlem3.b
    @41
    hdmapinvlem3.z
    grprid
    syl2anc
    3eqtrd
    wph
    @29
    @0
    @5
    cfv
    #
    cC
    @5
    cfv
    #
    @39
    co
    c.0
    @11
    @39
    co
    #
    @11
    wph
    c.pl
    @39
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @0
    cC
    cD
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.p
    hdmapinvlem3.r
    @41
    hdmapinvlem3.s
    hdmapinvlem3.k
    @35
    @36
    @27
    hdmaplna1
    wph
    c.0
    @59
    @11
    @60
    @39
    wph
    @59
    cI
    cE
    @5
    cfv
    #
    c.xp
    co
    cI
    c.0
    c.xp
    co
    #
    c.0
    wph
    cI
    cB
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
    cD
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.q
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.s
    hdmapinvlem3.k
    @22
    @27
    hdmapinvlem3.i
    hdmaplnm1
    wph
    @62
    c.0
    cI
    c.xp
    wph
    cB
    cD
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
    hdmapinvlem3.h
    hdmapinvlem3.e
    hdmapinvlem3.o
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.z
    hdmapinvlem3.s
    hdmapinvlem3.k
    hdmapinvlem3.d
    hdmapinvlem2
    oveq2d
    wph
    @49
    @34
    @63
    c.0
    wceq
    @50
    hdmapinvlem3.i
    cB
    cR
    c.xp
    cI
    c.0
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.z
    ringrz
    syl2anc
    3eqtrrd
    hdmapinvlem3.ij
    oveq12d
    wph
    @55
    @56
    @61
    @11
    wceq
    @57
    @58
    cB
    @39
    cR
    @11
    c.0
    hdmapinvlem3.b
    @41
    hdmapinvlem3.z
    grplid
    syl2anc
    3eqtr2d
    oveq12d
    eqtrd
    wph
    @55
    @56
    @13
    c.0
    wceq
    @57
    @58
    cB
    cR
    @12
    @11
    c.0
    hdmapinvlem3.b
    hdmapinvlem3.z
    @31
    grpsubid
    syl2anc
    3eqtrd
end
