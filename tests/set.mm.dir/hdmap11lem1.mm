include "cv.mm"
include "cfv.mm"
include "cotp.mm"
include "co.mm"
include "c0g.mm"
include "csn.mm"
include "eqid.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "hvmapcl2.mm"
include "eldifad.mm"
include "mapdhvmap.mm"
include "necomd.mm"
include "hdmap1cl.mm"
include "clss.mm"
include "cpr.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "lssneln0.mm"
include "wceq.mm"
include "csg.mm"
include "wa.mm"
include "eqidd.mm"
include "hdmap1eq.mm"
include "mpbid.mm"
include "simpld.mm"
include "hdmap1l6.mm"
include "clmod.mm"
include "wcel.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "dvhlvec.mm"
include "lspprvacl.mm"
include "lspsnel5a.mm"
include "ssneldd.mm"
include "lspsnne2.mm"
include "hdmaplem4.mm"
include "hdmapval2.mm"
include "wne.mm"
include "lspindpi.mm"
include "simprd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem hdmap11lem1
  let wph: wff ph
  let vz: setvar z
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cS: class S
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmap11.h: |- H = ( LHyp ` K )
  assume hdmap11.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap11.v: |- V = ( Base ` U )
  assume hdmap11.p: |- .+ = ( +g ` U )
  assume hdmap11.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap11.a: |- .+b = ( +g ` C )
  assume hdmap11.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap11.x: |- ( ph -> X e. V )
  assume hdmap11.y: |- ( ph -> Y e. V )
  assume hdmap11.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmap11.o: |- .0. = ( 0g ` U )
  assume hdmap11.n: |- N = ( LSpan ` U )
  assume hdmap11.d: |- D = ( Base ` C )
  assume hdmap11.l: |- L = ( LSpan ` C )
  assume hdmap11.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap11.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmap11.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap11lem0.1a: |- ( ph -> z e. V )
  assume hdmap11lem0.6: |- ( ph -> -. z e. ( N ` { X , Y } ) )
  assume hdmap11lem0.2a: |- ( ph -> ( N ` { z } ) =/= ( N ` { E } ) )


  assert |- ( ph -> ( S ` ( X .+ Y ) ) = ( ( S ` X ) .+b ( S ` Y ) ) )

  proof
    wph
    vz
    cv
    #
    cE
    cE
    cJ
    cfv
    #
    @0
    cotp
    cI
    cfv
    #
    cX
    cY
    c.pl
    co
    #
    cotp
    cI
    cfv
    @0
    @2
    cX
    cotp
    cI
    cfv
    #
    @0
    @2
    cY
    cotp
    cI
    cfv
    #
    c.pb
    co
    @3
    cS
    cfv
    cX
    cS
    cfv
    #
    cY
    cS
    cfv
    #
    c.pb
    co
    wph
    cC
    cD
    c.pl
    c.pb
    cU
    @2
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    @0
    cX
    c.0
    cY
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.p
    hdmap11.o
    hdmap11.n
    hdmap11.c
    hdmap11.d
    hdmap11.a
    hdmap11.l
    hdmap11.m
    hdmap11.i
    hdmap11.k
    wph
    cC
    cD
    cU
    @1
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cE
    @0
    c.0
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.o
    hdmap11.n
    hdmap11.c
    hdmap11.d
    hdmap11.l
    hdmap11.m
    hdmap11.i
    hdmap11.k
    wph
    @1
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
    @8
    cV
    cW
    cE
    c.0
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.o
    hdmap11.c
    hdmap11.d
    @8
    eqid
    hdmap11.j
    hdmap11.k
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
    c.0
    hdmap11.h
    @9
    eqid
    @10
    eqid
    hdmap11.u
    hdmap11.v
    hdmap11.o
    hdmap11.e
    hdmap11.k
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
    cL
    cK
    cM
    cN
    cV
    cW
    cE
    c.0
    hdmap11.h
    hdmap11.u
    hdmap11.v
    hdmap11.o
    hdmap11.n
    hdmap11.c
    hdmap11.l
    hdmap11.m
    hdmap11.j
    hdmap11.k
    @11
    mapdhvmap
    #
    wph
    @0
    csn
    cN
    cfv
    #
    cE
    csn
    cN
    cfv
    hdmap11lem0.2a
    necomd
    #
    @11
    hdmap11lem0.1a
    hdmap1cl
    #
    wph
    cU
    clss
    cfv
    #
    cX
    cY
    cpr
    cN
    cfv
    #
    cV
    cU
    @0
    c.0
    hdmap11.v
    hdmap11.o
    @17
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    hdmap11.h
    hdmap11.u
    hdmap11.k
    dvhlmod
    #
    wph
    @17
    cN
    cV
    cU
    cX
    cY
    hdmap11.v
    @19
    hdmap11.n
    @20
    hdmap11.x
    hdmap11.y
    lspprcl
    #
    hdmap11lem0.1a
    hdmap11lem0.6
    lssneln0
    #
    hdmap11.x
    hdmap11.y
    hdmap11lem0.6
    wph
    @14
    cM
    cfv
    @2
    csn
    cL
    cfv
    wceq
    #
    cE
    @0
    cU
    csg
    cfv
    #
    co
    csn
    cN
    cfv
    cM
    cfv
    @1
    @2
    cC
    csg
    cfv
    #
    co
    csn
    cL
    cfv
    wceq
    #
    wph
    @2
    @2
    wceq
    @23
    @26
    wa
    wph
    @2
    eqidd
    wph
    cC
    cD
    @25
    cU
    @1
    @2
    cH
    cI
    cK
    cL
    cM
    @24
    cN
    cV
    cW
    cE
    @0
    c.0
    hdmap11.h
    hdmap11.u
    hdmap11.v
    @24
    eqid
    hdmap11.o
    hdmap11.n
    hdmap11.c
    hdmap11.d
    @25
    eqid
    hdmap11.l
    hdmap11.m
    hdmap11.i
    hdmap11.k
    @11
    @12
    @22
    @16
    @15
    @13
    hdmap1eq
    mpbid
    simpld
    hdmap1l6
    wph
    cC
    cD
    cS
    @3
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    @0
    hdmap11.h
    hdmap11.e
    hdmap11.u
    hdmap11.v
    hdmap11.n
    hdmap11.c
    hdmap11.d
    hdmap11.j
    hdmap11.i
    hdmap11.s
    hdmap11.k
    wph
    cU
    clmod
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    @3
    cV
    wcel
    @20
    hdmap11.x
    hdmap11.y
    c.pl
    cV
    cU
    cX
    cY
    hdmap11.v
    hdmap11.p
    lmodvacl
    syl3anc
    #
    hdmap11lem0.1a
    wph
    cN
    cV
    cU
    cE
    @3
    c.0
    @0
    hdmap11.v
    hdmap11.n
    hdmap11.o
    wph
    cU
    cH
    cK
    cW
    hdmap11.h
    hdmap11.u
    hdmap11.k
    dvhlvec
    #
    wph
    cE
    cV
    c.0
    csn
    @11
    eldifad
    #
    @27
    @22
    hdmap11lem0.2a
    wph
    cN
    cV
    cU
    @0
    @3
    hdmap11.v
    hdmap11.n
    @20
    hdmap11lem0.1a
    @27
    wph
    @3
    csn
    cN
    cfv
    @18
    @0
    wph
    @17
    @18
    cN
    cU
    @3
    @19
    hdmap11.n
    @20
    @21
    wph
    c.pl
    cN
    cV
    cU
    cX
    cY
    hdmap11.v
    hdmap11.p
    hdmap11.n
    @20
    hdmap11.x
    hdmap11.y
    lspprvacl
    lspsnel5a
    hdmap11lem0.6
    ssneldd
    lspsnne2
    hdmaplem4
    hdmapval2
    wph
    @6
    @4
    @7
    @5
    c.pb
    wph
    cC
    cD
    cS
    cX
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    @0
    hdmap11.h
    hdmap11.e
    hdmap11.u
    hdmap11.v
    hdmap11.n
    hdmap11.c
    hdmap11.d
    hdmap11.j
    hdmap11.i
    hdmap11.s
    hdmap11.k
    hdmap11.x
    hdmap11lem0.1a
    wph
    cN
    cV
    cU
    cE
    cX
    c.0
    @0
    hdmap11.v
    hdmap11.n
    hdmap11.o
    @28
    @29
    hdmap11.x
    @22
    hdmap11lem0.2a
    wph
    @14
    cX
    csn
    cN
    cfv
    wne
    #
    @14
    cY
    csn
    cN
    cfv
    wne
    #
    wph
    cN
    cV
    cU
    @0
    cX
    cY
    hdmap11.v
    hdmap11.n
    @28
    hdmap11lem0.1a
    hdmap11.x
    hdmap11.y
    hdmap11lem0.6
    lspindpi
    #
    simpld
    hdmaplem4
    hdmapval2
    wph
    cC
    cD
    cS
    cY
    cU
    cE
    cH
    cI
    cJ
    cK
    cN
    cV
    cW
    @0
    hdmap11.h
    hdmap11.e
    hdmap11.u
    hdmap11.v
    hdmap11.n
    hdmap11.c
    hdmap11.d
    hdmap11.j
    hdmap11.i
    hdmap11.s
    hdmap11.k
    hdmap11.y
    hdmap11lem0.1a
    wph
    cN
    cV
    cU
    cE
    cY
    c.0
    @0
    hdmap11.v
    hdmap11.n
    hdmap11.o
    @28
    @29
    hdmap11.y
    @22
    hdmap11lem0.2a
    wph
    @30
    @31
    @32
    simprd
    hdmaplem4
    hdmapval2
    oveq12d
    3eqtr4d
end
