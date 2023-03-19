include "cotp.mm"
include "cfv.mm"
include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "lmodgrp.mm"
include "syl.mm"
include "csn.mm"
include "wne.mm"
include "dvhlvec.mm"
include "eldifad.mm"
include "dvhlmod.mm"
include "lmod0vcl.mm"
include "eqeltrd.mm"
include "lspindpi.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "grprid.mm"
include "syl2anc.mm"
include "oteq3d.mm"
include "fveq2d.mm"
include "cdif.mm"
include "mapdhval0.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"

theorem mapdh6cN
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let cG: class G
  let vw: setvar w
  let cE: class E
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.h: |- H = ( LHyp ` K )
  assume mapdh.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh.v: |- V = ( Base ` U )
  assume mapdh.s: |- .- = ( -g ` U )
  assume mapdhc.o: |- .0. = ( 0g ` U )
  assume mapdh.n: |- N = ( LSpan ` U )
  assume mapdh.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh.d: |- D = ( Base ` C )
  assume mapdh.r: |- R = ( -g ` C )
  assume mapdh.j: |- J = ( LSpan ` C )
  assume mapdh.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhc.f: |- ( ph -> F e. D )
  assume mapdh.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdhcl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh.p: |- .+ = ( +g ` U )
  assume mapdh.a: |- .+b = ( +g ` C )
  assume mapdh6c.y: |- ( ph -> Y e. V )
  assume mapdh6c.z: |- ( ph -> Z = .0. )
  assume mapdh6c.ne: |- ( ph -> -. X e. ( N ` { Y , Z } ) )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  disjoint .0. h
  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint U h
  disjoint .- h
  disjoint Z h
  disjoint Z x
  disjoint G h
  disjoint h w
  disjoint G x
  disjoint E h
  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    #
    cQ
    c.pb
    co
    #
    @1
    @1
    cX
    cF
    cZ
    cotp
    #
    cI
    cfv
    #
    c.pb
    co
    cX
    cF
    cY
    cZ
    c.pl
    co
    #
    cotp
    #
    cI
    cfv
    wph
    cC
    cgrp
    wcel
    #
    @1
    cD
    wcel
    @2
    @1
    wceq
    wph
    cC
    clmod
    wcel
    @7
    wph
    cC
    cH
    cK
    cW
    mapdh.h
    mapdh.c
    mapdh.k
    lcdlmod
    cC
    lmodgrp
    syl
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    mapdh6c.y
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    wne
    @8
    cZ
    csn
    cN
    cfv
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    mapdh.v
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlvec
    wph
    cX
    cV
    c.0
    csn
    #
    mapdhcl.x
    eldifad
    mapdh6c.y
    wph
    cZ
    c.0
    cV
    mapdh6c.z
    wph
    cU
    clmod
    wcel
    #
    c.0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlmod
    #
    cV
    cU
    c.0
    mapdh.v
    mapdhc.o
    lmod0vcl
    syl
    eqeltrd
    mapdh6c.ne
    lspindpi
    simpld
    mapdhcl
    cD
    c.pb
    cC
    @1
    cQ
    mapdh.d
    mapdh.a
    mapdh.q
    grprid
    syl2anc
    wph
    @4
    cQ
    @1
    c.pb
    wph
    @4
    cX
    cF
    c.0
    cotp
    #
    cI
    cfv
    cQ
    wph
    @3
    @12
    cI
    wph
    cZ
    c.0
    cX
    cF
    mapdh6c.z
    oteq3d
    fveq2d
    wph
    vx
    cV
    @9
    cdif
    cD
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cX
    c.0
    mapdh.q
    mapdh.i
    mapdhc.o
    mapdhcl.x
    mapdhc.f
    mapdhval0
    eqtrd
    oveq2d
    wph
    @6
    @0
    cI
    wph
    @5
    cY
    cX
    cF
    wph
    @5
    cY
    c.0
    c.pl
    co
    #
    cY
    wph
    cZ
    c.0
    cY
    c.pl
    mapdh6c.z
    oveq2d
    wph
    cU
    cgrp
    wcel
    #
    cY
    cV
    wcel
    @13
    cY
    wceq
    wph
    @10
    @14
    @11
    cU
    lmodgrp
    syl
    mapdh6c.y
    cV
    c.pl
    cU
    cY
    c.0
    mapdh.v
    mapdh.p
    mapdhc.o
    grprid
    syl2anc
    eqtrd
    oteq3d
    fveq2d
    3eqtr4rd
end
