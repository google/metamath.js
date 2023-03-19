include "cphl.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "clsm.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "wral.mm"
include "chs.mm"
include "hlhilphllem.mm"
include "wa.mm"
include "coch.mm"
include "chlt.mm"
include "adantr.mm"
include "eqid.mm"
include "cdih.mm"
include "crn.mm"
include "wss.mm"
include "hlhillcs.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "dihrnss.mm"
include "sylan.mm"
include "syldan.mm"
include "hlhilocv.mm"
include "oveq2d.mm"
include "hlhillsm.mm"
include "oveqd.mm"
include "clss.mm"
include "dihrnlss.mm"
include "wi.mm"
include "dochoccl.mm"
include "biimpd.mm"
include "ex.mm"
include "pm2.43d.mm"
include "imp.mm"
include "dochexmid.mm"
include "3eqtr3d.mm"
include "hlhilbase.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "ishil2.mm"
include "sylanbrc.mm"

theorem hlhilhillem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.xi: class .,
  let cJ: class J
  let cK: class K
  let cL: class L
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume hlhilphl.h: |- H = ( LHyp ` K )
  assume hlhilphllem.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilphl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilphllem.f: |- F = ( Scalar ` U )
  assume hlhilphllem.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilphllem.v: |- V = ( Base ` L )
  assume hlhilphllem.a: |- .+ = ( +g ` L )
  assume hlhilphllem.s: |- .x. = ( .s ` L )
  assume hlhilphllem.r: |- R = ( Scalar ` L )
  assume hlhilphllem.b: |- B = ( Base ` R )
  assume hlhilphllem.p: |- .+^ = ( +g ` R )
  assume hlhilphllem.t: |- .X. = ( .r ` R )
  assume hlhilphllem.q: |- Q = ( 0g ` R )
  assume hlhilphllem.z: |- .0. = ( 0g ` L )
  assume hlhilphllem.i: |- ., = ( .i ` U )
  assume hlhilphllem.j: |- J = ( ( HDMap ` K ) ` W )
  assume hlhilphllem.g: |- G = ( ( HGMap ` K ) ` W )
  assume hlhilphllem.e: |- E = ( x e. V , y e. V |-> ( ( J ` y ) ` x ) )
  assume hlhilphllem.o: |- O = ( ocv ` U )
  assume hlhilphllem.c: |- C = ( CSubSp ` U )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint V x
  disjoint V y
  disjoint C x
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint U x
  disjoint W x
  disjoint W y
  disjoint ph x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint B b
  disjoint c d
  disjoint B c
  disjoint B d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a x
  disjoint a y
  disjoint V a
  disjoint b x
  disjoint b y
  disjoint V b
  disjoint c x
  disjoint c y
  disjoint V c
  disjoint d x
  disjoint d y
  disjoint V d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  assert |- ( ph -> U e. Hil )

  proof
    wph
    cU
    cphl
    wcel
    vx
    cv
    #
    @0
    cO
    cfv
    #
    cU
    clsm
    cfv
    #
    co
    #
    cU
    cbs
    cfv
    #
    wceq
    #
    vx
    cC
    wral
    cU
    chs
    wcel
    wph
    vx
    vy
    cB
    c.pl
    c.pd
    cQ
    cR
    c.x
    c.xp
    cU
    cE
    cF
    cG
    cH
    c.xi
    cJ
    cK
    cL
    cV
    cW
    c.0
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    hlhilphllem.f
    hlhilphllem.l
    hlhilphllem.v
    hlhilphllem.a
    hlhilphllem.s
    hlhilphllem.r
    hlhilphllem.b
    hlhilphllem.p
    hlhilphllem.t
    hlhilphllem.q
    hlhilphllem.z
    hlhilphllem.i
    hlhilphllem.j
    hlhilphllem.g
    hlhilphllem.e
    hlhilphllem
    wph
    @5
    vx
    cC
    wph
    @0
    cC
    wcel
    #
    wa
    #
    @3
    cV
    @4
    @7
    @0
    @1
    cL
    clsm
    cfv
    #
    co
    @0
    @0
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @8
    co
    #
    @3
    cV
    @7
    @1
    @10
    @0
    @8
    @7
    cU
    cH
    cK
    cL
    @9
    cO
    cV
    cW
    @0
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.u
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @6
    hlhilphl.k
    adantr
    hlhilphllem.v
    @9
    eqid
    #
    hlhilphllem.o
    wph
    @6
    @0
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    wcel
    #
    @0
    cV
    wss
    #
    wph
    @6
    @16
    wph
    cC
    @15
    @0
    wph
    cC
    cU
    cH
    @14
    cK
    cW
    hlhilphl.h
    @14
    eqid
    #
    hlhilphllem.u
    hlhilphllem.c
    hlhilphl.k
    hlhillcs
    eleq2d
    biimpa
    #
    wph
    @12
    @16
    @17
    hlhilphl.k
    cL
    cH
    @14
    cK
    cV
    cW
    @0
    hlhilphl.h
    hlhilphllem.l
    @18
    hlhilphllem.v
    dihrnss
    sylan
    #
    syldan
    hlhilocv
    oveq2d
    @7
    @8
    @2
    @0
    @1
    wph
    @8
    @2
    wceq
    @6
    wph
    @8
    cU
    cH
    cK
    cL
    cW
    hlhilphl.h
    hlhilphllem.l
    hlhilphllem.u
    hlhilphl.k
    @8
    eqid
    #
    hlhillsm
    adantr
    oveqd
    wph
    @6
    @16
    @11
    cV
    wceq
    @19
    wph
    @16
    wa
    #
    @8
    cL
    clss
    cfv
    #
    cL
    cH
    cK
    @9
    cV
    cW
    @0
    hlhilphl.h
    @13
    hlhilphllem.l
    hlhilphllem.v
    @23
    eqid
    #
    @21
    wph
    @12
    @16
    hlhilphl.k
    adantr
    #
    wph
    @12
    @16
    @0
    @23
    wcel
    hlhilphl.k
    @23
    cL
    cH
    @14
    cK
    cW
    @0
    hlhilphl.h
    hlhilphllem.l
    @18
    @24
    dihrnlss
    sylan
    wph
    @16
    @10
    @9
    cfv
    @0
    wceq
    #
    wph
    @16
    @26
    wph
    @16
    @16
    @26
    wi
    @22
    @16
    @26
    @22
    cL
    cH
    @14
    cK
    @9
    cV
    cW
    @0
    hlhilphl.h
    @18
    hlhilphllem.l
    hlhilphllem.v
    @13
    @25
    @20
    dochoccl
    biimpd
    ex
    pm2.43d
    imp
    dochexmid
    syldan
    3eqtr3d
    wph
    cV
    @4
    wceq
    @6
    wph
    cU
    cH
    cK
    cL
    cV
    cW
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    hlhilphllem.l
    hlhilphllem.v
    hlhilbase
    adantr
    eqtrd
    ralrimiva
    cC
    @2
    cU
    cO
    @4
    vx
    @4
    eqid
    @2
    eqid
    hlhilphllem.o
    hlhilphllem.c
    ishil2
    sylanbrc
end
