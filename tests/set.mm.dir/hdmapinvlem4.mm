include "cfv.mm"
include "co.mm"
include "csg.mm"
include "wceq.mm"
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
include "lmodvacl.mm"
include "hdmaplns1.mm"
include "hdmapinvlem3.mm"
include "lmodvsubcl.mm"
include "hdmapip0com.mm"
include "mpbid.mm"
include "hdmaplnm1.mm"
include "cplusg.mm"
include "hdmaplna2.mm"
include "hdmapinvlem2.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "hdmapipcl.mm"
include "grprid.mm"
include "hdmapglnm2.mm"
include "cur.mm"
include "chvm.mm"
include "hdmapevec2.mm"
include "oveq1d.mm"
include "hgmapcl.mm"
include "ringlidm.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "hdmapinvlem1.mm"
include "ringlz.mm"
include "grplid.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "lmodmcl.mm"
include "grpsubeq0.mm"

theorem hdmapinvlem4
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


  assert |- ( ph -> ( J .X. ( G ` I ) ) = ( ( S ` C ) ` D ) )

  proof
    wph
    cJ
    cI
    cG
    cfv
    #
    c.xp
    co
    #
    cD
    cC
    cS
    cfv
    #
    cfv
    #
    cR
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @1
    @3
    wceq
    #
    wph
    cJ
    cE
    c.x
    co
    #
    cD
    c.mi
    co
    #
    cI
    cE
    c.x
    co
    #
    cC
    c.pl
    co
    #
    cS
    cfv
    #
    cfv
    #
    @8
    @12
    cfv
    #
    cD
    @12
    cfv
    #
    @4
    co
    c.0
    @5
    wph
    cR
    cS
    cU
    cH
    cK
    c.mi
    @4
    cV
    cW
    @8
    cD
    @11
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.m
    hdmapinvlem3.r
    @4
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
    #
    cE
    cV
    wcel
    #
    @8
    cV
    wcel
    #
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
    @22
    hdmapinvlem3.h
    @23
    eqid
    @24
    eqid
    hdmapinvlem3.u
    hdmapinvlem3.v
    @22
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
    @27
    cV
    wss
    @28
    cV
    wss
    hdmapinvlem3.k
    wph
    cE
    cV
    @25
    snssd
    cU
    cH
    cK
    cO
    cV
    cW
    @27
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
    wph
    @17
    @10
    cV
    wcel
    #
    cC
    cV
    wcel
    @11
    cV
    wcel
    @21
    wph
    @17
    cI
    cB
    wcel
    @19
    @31
    @21
    hdmapinvlem3.i
    @25
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
    @28
    cV
    cC
    @29
    hdmapinvlem3.c
    sseldd
    #
    c.pl
    cV
    cU
    @10
    cC
    hdmapinvlem3.v
    hdmapinvlem3.p
    lmodvacl
    syl3anc
    #
    hdmaplns1
    wph
    @11
    @9
    cS
    cfv
    cfv
    c.0
    wceq
    @13
    c.0
    wceq
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
    cI
    cJ
    cK
    c.mi
    cO
    cV
    cW
    c.0
    hdmapinvlem3.h
    hdmapinvlem3.e
    hdmapinvlem3.o
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.p
    hdmapinvlem3.m
    hdmapinvlem3.q
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.z
    hdmapinvlem3.s
    hdmapinvlem3.g
    hdmapinvlem3.k
    hdmapinvlem3.c
    hdmapinvlem3.d
    hdmapinvlem3.i
    hdmapinvlem3.j
    hdmapinvlem3.ij
    hdmapinvlem3
    wph
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @9
    @11
    c.0
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.z
    hdmapinvlem3.s
    hdmapinvlem3.k
    wph
    @17
    @20
    cD
    cV
    wcel
    @9
    cV
    wcel
    @21
    @26
    @30
    c.mi
    cV
    cU
    @8
    cD
    hdmapinvlem3.v
    hdmapinvlem3.m
    lmodvsubcl
    syl3anc
    @34
    hdmapip0com
    mpbid
    wph
    @14
    @1
    @15
    @3
    @4
    wph
    @14
    cJ
    cE
    @12
    cfv
    #
    c.xp
    co
    @1
    wph
    cJ
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
    @11
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.q
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.s
    hdmapinvlem3.k
    @25
    @34
    hdmapinvlem3.j
    hdmaplnm1
    wph
    @35
    @0
    cJ
    c.xp
    wph
    @35
    cE
    @10
    cS
    cfv
    #
    cfv
    #
    cE
    @2
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    @37
    c.0
    @39
    co
    #
    @0
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
    cE
    @10
    cC
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
    @25
    @32
    @33
    hdmaplna2
    wph
    @38
    c.0
    @37
    @39
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
    hdmapinvlem2
    oveq2d
    wph
    @40
    @37
    cE
    cE
    cS
    cfv
    #
    cfv
    #
    @0
    c.xp
    co
    #
    @0
    wph
    cR
    cgrp
    wcel
    #
    @37
    cB
    wcel
    @40
    @37
    wceq
    wph
    cR
    crg
    wcel
    #
    @45
    wph
    @17
    @46
    @21
    cR
    cU
    hdmapinvlem3.r
    lmodring
    syl
    #
    cR
    ringgrp
    syl
    #
    wph
    cB
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cE
    @10
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.s
    hdmapinvlem3.k
    @25
    @32
    hdmapipcl
    cB
    @39
    cR
    @37
    c.0
    hdmapinvlem3.b
    @41
    hdmapinvlem3.z
    grprid
    syl2anc
    wph
    cI
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
    hdmapinvlem3.g
    hdmapinvlem3.k
    @25
    @25
    hdmapinvlem3.i
    hdmapglnm2
    wph
    @44
    cR
    cur
    cfv
    #
    @0
    c.xp
    co
    #
    @0
    wph
    @43
    @49
    @0
    c.xp
    wph
    cR
    cS
    cU
    @49
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
    @51
    eqid
    hdmapinvlem3.s
    hdmapinvlem3.k
    hdmapinvlem3.u
    hdmapinvlem3.r
    @49
    eqid
    #
    hdmapevec2
    oveq1d
    wph
    @46
    @0
    cB
    wcel
    #
    @50
    @0
    wceq
    @47
    wph
    cB
    cR
    cU
    cI
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
    hdmapinvlem3.i
    hgmapcl
    #
    cB
    cR
    c.xp
    @49
    @0
    hdmapinvlem3.b
    hdmapinvlem3.t
    @52
    ringlidm
    syl2anc
    eqtrd
    3eqtrd
    3eqtrd
    oveq2d
    eqtrd
    wph
    @15
    cD
    @36
    cfv
    #
    @3
    @39
    co
    c.0
    @3
    @39
    co
    #
    @3
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
    cD
    @10
    cC
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.p
    hdmapinvlem3.r
    @41
    hdmapinvlem3.s
    hdmapinvlem3.k
    @30
    @32
    @33
    hdmaplna2
    wph
    @55
    c.0
    @3
    @39
    wph
    @55
    cD
    @42
    cfv
    #
    @0
    c.xp
    co
    c.0
    @0
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
    cG
    cH
    cK
    cV
    cW
    cD
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
    @30
    @25
    hdmapinvlem3.i
    hdmapglnm2
    wph
    @57
    c.0
    @0
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
    hdmapinvlem1
    oveq1d
    wph
    @46
    @53
    @58
    c.0
    wceq
    @47
    @54
    cB
    cR
    c.xp
    @0
    c.0
    hdmapinvlem3.b
    hdmapinvlem3.t
    hdmapinvlem3.z
    ringlz
    syl2anc
    3eqtrd
    oveq1d
    wph
    @45
    @3
    cB
    wcel
    #
    @56
    @3
    wceq
    @48
    wph
    cB
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cD
    cC
    hdmapinvlem3.h
    hdmapinvlem3.u
    hdmapinvlem3.v
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.s
    hdmapinvlem3.k
    @30
    @33
    hdmapipcl
    #
    cB
    @39
    cR
    @3
    c.0
    hdmapinvlem3.b
    @41
    hdmapinvlem3.z
    grplid
    syl2anc
    3eqtrd
    oveq12d
    3eqtr3rd
    wph
    @45
    @1
    cB
    wcel
    #
    @59
    @6
    @7
    wb
    @48
    wph
    @17
    @18
    @53
    @61
    @21
    hdmapinvlem3.j
    @54
    c.xp
    cR
    cB
    cU
    cJ
    @0
    hdmapinvlem3.r
    hdmapinvlem3.b
    hdmapinvlem3.t
    lmodmcl
    syl3anc
    @60
    cB
    cR
    @4
    @1
    @3
    c.0
    hdmapinvlem3.b
    hdmapinvlem3.z
    @16
    grpsubeq0
    syl3anc
    mpbid
end
