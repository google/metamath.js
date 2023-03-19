include "cfv.mm"
include "cotp.mm"
include "cv.mm"
include "clspn.mm"
include "cmpd.mm"
include "c0g.mm"
include "eqid.mm"
include "csn.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "hvmapcl2.mm"
include "eldifad.mm"
include "mapdhvmap.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "hdmap1cl.mm"
include "wceq.mm"
include "csg.mm"
include "co.mm"
include "wa.mm"
include "eqidd.mm"
include "clss.mm"
include "cpr.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "lssneln0.mm"
include "hdmap1eq.mm"
include "mpbid.mm"
include "cun.mm"
include "lspprid1.mm"
include "lspsnel5a.mm"
include "unssd.mm"
include "ssneldd.mm"
include "hdmapval2.mm"
include "hdmapevec.mm"
include "eqtr3d.mm"
include "lspprid2.mm"
include "eqcomd.mm"
include "hdmap1eq4N.mm"

theorem hdmapval3lemN
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume hdmapval3.h: |- H = ( LHyp ` K )
  assume hdmapval3.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapval3.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapval3.v: |- V = ( Base ` U )
  assume hdmapval3.n: |- N = ( LSpan ` U )
  assume hdmapval3.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapval3.d: |- D = ( Base ` C )
  assume hdmapval3.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapval3.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmapval3.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapval3.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapval3.te: |- ( ph -> ( N ` { T } ) =/= ( N ` { E } ) )
  assume hdmapval3lem.t: |- ( ph -> T e. ( V \ { ( 0g ` U ) } ) )
  assume hdmapval3lem.x: |- ( ph -> x e. V )
  assume hdmapval3lem.xn: |- ( ph -> -. x e. ( N ` { E , T } ) )


  assert |- ( ph -> ( S ` T ) = ( I ` <. E , ( J ` E ) , T >. ) )

  proof
    wph
    cE
    cE
    cJ
    cfv
    #
    cT
    cotp
    cI
    cfv
    cT
    cS
    cfv
    #
    wph
    @1
    cC
    cD
    cU
    cE
    @0
    vx
    cv
    #
    cotp
    cI
    cfv
    #
    @0
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
    @2
    cE
    cU
    c0g
    cfv
    #
    cT
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @6
    eqid
    #
    hdmapval3.n
    hdmapval3.c
    hdmapval3.d
    @4
    eqid
    #
    @5
    eqid
    #
    hdmapval3.i
    hdmapval3.k
    wph
    cC
    cD
    cU
    @0
    cH
    cI
    cK
    @4
    @5
    cN
    cV
    cW
    cE
    @2
    @6
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @7
    hdmapval3.n
    hdmapval3.c
    hdmapval3.d
    @8
    @9
    hdmapval3.i
    hdmapval3.k
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
    @10
    cV
    cW
    cE
    @6
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @7
    hdmapval3.c
    hdmapval3.d
    @10
    eqid
    hdmapval3.j
    hdmapval3.k
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
    @6
    hdmapval3.h
    @11
    eqid
    @12
    eqid
    hdmapval3.u
    hdmapval3.v
    @7
    hdmapval3.e
    hdmapval3.k
    dvheveccl
    #
    hvmapcl2
    eldifad
    #
    wph
    cC
    cJ
    cU
    cH
    @4
    cK
    @5
    cN
    cV
    cW
    cE
    @6
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @7
    hdmapval3.n
    hdmapval3.c
    @8
    @9
    hdmapval3.j
    hdmapval3.k
    @13
    mapdhvmap
    #
    wph
    @2
    csn
    cN
    cfv
    #
    cE
    csn
    cN
    cfv
    #
    wph
    @16
    @17
    wne
    @16
    cT
    csn
    cN
    cfv
    #
    wne
    wph
    cN
    cV
    cU
    @2
    cE
    cT
    hdmapval3.v
    hdmapval3.n
    wph
    cU
    cH
    cK
    cW
    hdmapval3.h
    hdmapval3.u
    hdmapval3.k
    dvhlvec
    hdmapval3lem.x
    wph
    cE
    cV
    @6
    csn
    #
    @13
    eldifad
    #
    wph
    cT
    cV
    @19
    hdmapval3lem.t
    eldifad
    #
    hdmapval3lem.xn
    lspindpi
    simpld
    necomd
    #
    @13
    hdmapval3lem.x
    hdmap1cl
    #
    wph
    @16
    @5
    cfv
    @3
    csn
    @4
    cfv
    wceq
    #
    cE
    @2
    cU
    csg
    cfv
    #
    co
    csn
    cN
    cfv
    @5
    cfv
    @0
    @3
    cC
    csg
    cfv
    #
    co
    csn
    @4
    cfv
    wceq
    #
    wph
    @3
    @3
    wceq
    @24
    @27
    wa
    wph
    @3
    eqidd
    wph
    cC
    cD
    @26
    cU
    @0
    @3
    cH
    cI
    cK
    @4
    @5
    @25
    cN
    cV
    cW
    cE
    @2
    @6
    hdmapval3.h
    hdmapval3.u
    hdmapval3.v
    @25
    eqid
    @7
    hdmapval3.n
    hdmapval3.c
    hdmapval3.d
    @26
    eqid
    @8
    @9
    hdmapval3.i
    hdmapval3.k
    @13
    @14
    wph
    cU
    clss
    cfv
    #
    cE
    cT
    cpr
    cN
    cfv
    #
    cV
    cU
    @2
    @6
    hdmapval3.v
    @7
    @28
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    hdmapval3.h
    hdmapval3.u
    hdmapval3.k
    dvhlmod
    #
    wph
    @28
    cN
    cV
    cU
    cE
    cT
    hdmapval3.v
    @30
    hdmapval3.n
    @31
    @20
    @21
    lspprcl
    #
    hdmapval3lem.x
    hdmapval3lem.xn
    lssneln0
    #
    @23
    @22
    @15
    hdmap1eq
    mpbid
    simpld
    @33
    @13
    hdmapval3lem.t
    wph
    @18
    @17
    hdmapval3.te
    necomd
    hdmapval3lem.xn
    wph
    cE
    cS
    cfv
    @2
    @3
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
    @2
    hdmapval3.h
    hdmapval3.e
    hdmapval3.u
    hdmapval3.v
    hdmapval3.n
    hdmapval3.c
    hdmapval3.d
    hdmapval3.j
    hdmapval3.i
    hdmapval3.s
    hdmapval3.k
    @20
    hdmapval3lem.x
    wph
    @17
    @17
    cun
    @29
    @2
    wph
    @17
    @17
    @29
    wph
    @28
    @29
    cN
    cU
    cE
    @30
    hdmapval3.n
    @31
    @32
    wph
    cN
    cV
    cU
    cE
    cT
    hdmapval3.v
    hdmapval3.n
    @31
    @20
    @21
    lspprid1
    lspsnel5a
    #
    @34
    unssd
    hdmapval3lem.xn
    ssneldd
    hdmapval2
    wph
    cS
    cE
    cH
    cJ
    cK
    cW
    hdmapval3.h
    hdmapval3.e
    hdmapval3.j
    hdmapval3.s
    hdmapval3.k
    hdmapevec
    eqtr3d
    wph
    @1
    @2
    @3
    cT
    cotp
    cI
    cfv
    wph
    cC
    cD
    cS
    cT
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    @2
    hdmapval3.h
    hdmapval3.e
    hdmapval3.u
    hdmapval3.v
    hdmapval3.n
    hdmapval3.c
    hdmapval3.d
    hdmapval3.j
    hdmapval3.i
    hdmapval3.s
    hdmapval3.k
    @21
    hdmapval3lem.x
    wph
    @17
    @18
    cun
    @29
    @2
    wph
    @17
    @18
    @29
    @34
    wph
    @28
    @29
    cN
    cU
    cT
    @30
    hdmapval3.n
    @31
    @32
    wph
    cN
    cV
    cU
    cE
    cT
    hdmapval3.v
    hdmapval3.n
    @31
    @20
    @21
    lspprid2
    lspsnel5a
    unssd
    hdmapval3lem.xn
    ssneldd
    hdmapval2
    eqcomd
    hdmap1eq4N
    eqcomd
end
