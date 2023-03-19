include "cfv.mm"
include "c0g.mm"
include "cmulr.mm"
include "co.mm"
include "cvsca.mm"
include "oveq2d.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodring.mm"
include "syl.mm"
include "cdr.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "clfn.mm"
include "cv.mm"
include "crab.mm"
include "eqid.mm"
include "lcfrlem10.mm"
include "lcfrlem22.mm"
include "lsatssv.mm"
include "sseldd.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "drnginvrcl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "ldual0vs.mm"
include "cgrp.mm"
include "cbs.mm"
include "ldualgrp.mm"
include "ldualelvbase.mm"
include "grpsubid1.mm"
include "syl5eq.mm"
include "csn.mm"
include "cdif.mm"
include "lcfrlem13.mm"
include "eldifsni.mm"
include "eqnetrd.mm"

theorem lcfrlem33
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  assume lcfrlem17.h: |- H = ( LHyp ` K )
  assume lcfrlem17.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem17.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem17.v: |- V = ( Base ` U )
  assume lcfrlem17.p: |- .+ = ( +g ` U )
  assume lcfrlem17.z: |- .0. = ( 0g ` U )
  assume lcfrlem17.n: |- N = ( LSpan ` U )
  assume lcfrlem17.a: |- A = ( LSAtoms ` U )
  assume lcfrlem17.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem17.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfrlem17.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfrlem17.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lcfrlem22.b: |- B = ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) )
  assume lcfrlem24.t: |- .x. = ( .s ` U )
  assume lcfrlem24.s: |- S = ( Scalar ` U )
  assume lcfrlem24.q: |- Q = ( 0g ` S )
  assume lcfrlem24.r: |- R = ( Base ` S )
  assume lcfrlem24.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcfrlem24.ib: |- ( ph -> I e. B )
  assume lcfrlem24.l: |- L = ( LKer ` U )
  assume lcfrlem25.d: |- D = ( LDual ` U )
  assume lcfrlem28.jn: |- ( ph -> ( ( J ` Y ) ` I ) =/= Q )
  assume lcfrlem29.i: |- F = ( invr ` S )
  assume lcfrlem30.m: |- .- = ( -g ` D )
  assume lcfrlem30.c: |- C = ( ( J ` X ) .- ( ( ( F ` ( ( J ` Y ) ` I ) ) ( .r ` S ) ( ( J ` X ) ` I ) ) ( .s ` D ) ( J ` Y ) ) )
  assume lcfrlem33.xi: |- ( ph -> ( ( J ` X ) ` I ) = Q )

  disjoint k v
  disjoint k w
  disjoint k x
  disjoint ._|_ k
  disjoint v w
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint S k
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint V v
  disjoint V x
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint .0. x
  disjoint J f
  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  disjoint R f
  disjoint .x. f
  disjoint U f
  disjoint V f
  disjoint X f
  disjoint Y f
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  assert |- ( ph -> C =/= ( 0g ` D ) )

  proof
    wph
    cC
    cX
    cJ
    cfv
    #
    cD
    c0g
    cfv
    #
    wph
    cC
    @0
    cI
    cY
    cJ
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    cI
    @0
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @2
    cD
    cvsca
    cfv
    #
    co
    #
    c.mi
    co
    #
    @0
    lcfrlem30.c
    wph
    @10
    @0
    @1
    c.mi
    co
    #
    @0
    wph
    @9
    @1
    @0
    c.mi
    wph
    @9
    cQ
    @2
    @8
    co
    @1
    wph
    @7
    cQ
    @2
    @8
    wph
    @7
    @4
    cQ
    @6
    co
    #
    cQ
    wph
    @5
    cQ
    @4
    @6
    lcfrlem33.xi
    oveq2d
    wph
    cS
    crg
    wcel
    #
    @4
    cR
    wcel
    #
    @12
    cQ
    wceq
    wph
    cU
    clmod
    wcel
    #
    @13
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    #
    cS
    cU
    lcfrlem24.s
    lmodring
    syl
    wph
    cS
    cdr
    wcel
    #
    @3
    cR
    wcel
    #
    @3
    cQ
    wne
    @14
    wph
    cU
    clvec
    wcel
    @17
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlvec
    cS
    cU
    lcfrlem24.s
    lvecdrng
    syl
    wph
    @15
    @2
    cU
    clfn
    cfv
    #
    wcel
    cI
    cV
    wcel
    @18
    @16
    wph
    vx
    vw
    vv
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @20
    wceq
    vf
    @19
    crab
    #
    cD
    c.pl
    @1
    cR
    cS
    c.x
    cU
    vf
    vk
    @19
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @19
    eqid
    #
    lcfrlem24.l
    lcfrlem25.d
    @1
    eqid
    #
    @21
    eqid
    #
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    #
    wph
    cB
    cV
    cI
    wph
    cA
    cB
    cV
    cU
    lcfrlem17.v
    lcfrlem17.a
    @16
    wph
    cA
    cB
    c.pl
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem22
    lsatssv
    lcfrlem24.ib
    sseldd
    cS
    @19
    @2
    cR
    cV
    cU
    cI
    clmod
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.v
    @22
    lflcl
    syl3anc
    lcfrlem28.jn
    cR
    cS
    cF
    @3
    cQ
    lcfrlem24.r
    lcfrlem24.q
    lcfrlem29.i
    drnginvrcl
    syl3anc
    cR
    cS
    @6
    @4
    cQ
    lcfrlem24.r
    @6
    eqid
    lcfrlem24.q
    ringrz
    syl2anc
    eqtrd
    oveq1d
    wph
    cD
    cS
    @8
    @19
    @2
    @1
    cU
    cQ
    @22
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem25.d
    @8
    eqid
    @23
    @16
    @25
    ldual0vs
    eqtrd
    oveq2d
    wph
    cD
    cgrp
    wcel
    @0
    cD
    cbs
    cfv
    #
    wcel
    @11
    @0
    wceq
    wph
    cD
    cU
    lcfrlem25.d
    @16
    ldualgrp
    wph
    cD
    @19
    @0
    @26
    cU
    clmod
    @22
    lcfrlem25.d
    @26
    eqid
    #
    @16
    wph
    vx
    vw
    vv
    @21
    cD
    c.pl
    @1
    cR
    cS
    c.x
    cU
    vf
    vk
    @19
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @22
    lcfrlem24.l
    lcfrlem25.d
    @23
    @24
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem10
    ldualelvbase
    @26
    cD
    c.mi
    @0
    @1
    @27
    @23
    lcfrlem30.m
    grpsubid1
    syl2anc
    eqtrd
    syl5eq
    wph
    @0
    @21
    @1
    csn
    cdif
    wcel
    @0
    @1
    wne
    wph
    vx
    vw
    vv
    @21
    cD
    c.pl
    @1
    cR
    cS
    c.x
    cU
    vf
    vk
    @19
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @22
    lcfrlem24.l
    lcfrlem25.d
    @23
    @24
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem13
    @0
    @21
    @1
    eldifsni
    syl
    eqnetrd
end
