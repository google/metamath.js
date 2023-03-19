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
include "simprd.mm"
include "hdmap1cl.mm"
include "grplid.mm"
include "syl2anc.mm"
include "oteq3d.mm"
include "fveq2d.mm"
include "hdmap1val0.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtr4rd.mm"

theorem hdmap1l6b
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmap1l6.h: |- H = ( LHyp ` K )
  assume hdmap1l6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1l6.v: |- V = ( Base ` U )
  assume hdmap1l6.p: |- .+ = ( +g ` U )
  assume hdmap1l6.s: |- .- = ( -g ` U )
  assume hdmap1l6c.o: |- .0. = ( 0g ` U )
  assume hdmap1l6.n: |- N = ( LSpan ` U )
  assume hdmap1l6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1l6.d: |- D = ( Base ` C )
  assume hdmap1l6.a: |- .+b = ( +g ` C )
  assume hdmap1l6.r: |- R = ( -g ` C )
  assume hdmap1l6.q: |- Q = ( 0g ` C )
  assume hdmap1l6.l: |- L = ( LSpan ` C )
  assume hdmap1l6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1l6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1l6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1l6.f: |- ( ph -> F e. D )
  assume hdmap1l6cl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1l6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1l6b.y: |- ( ph -> Y = .0. )
  assume hdmap1l6b.z: |- ( ph -> Z e. V )
  assume hdmap1l6b.ne: |- ( ph -> -. X e. ( N ` { Y , Z } ) )


  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cQ
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
    #
    @1
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    #
    @1
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
    hdmap1l6.h
    hdmap1l6.c
    hdmap1l6.k
    lcdlmod
    cC
    lmodgrp
    syl
    wph
    cC
    cD
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    cZ
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    hdmap1l6.mn
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
    hdmap1l6.v
    hdmap1l6.n
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlvec
    wph
    cX
    cV
    c.0
    csn
    hdmap1l6cl.x
    eldifad
    #
    wph
    cY
    c.0
    cV
    hdmap1l6b.y
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
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    #
    cV
    cU
    c.0
    hdmap1l6.v
    hdmap1l6c.o
    lmod0vcl
    syl
    eqeltrd
    hdmap1l6b.z
    hdmap1l6b.ne
    lspindpi
    simprd
    hdmap1l6cl.x
    hdmap1l6b.z
    hdmap1cl
    cD
    c.pb
    cC
    @1
    cQ
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.q
    grplid
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
    cY
    c.0
    cX
    cF
    hdmap1l6b.y
    oteq3d
    fveq2d
    wph
    cC
    cD
    cQ
    cU
    cF
    cH
    cI
    cK
    cV
    cW
    cX
    c.0
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6c.o
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.q
    hdmap1l6.i
    hdmap1l6.k
    hdmap1l6.f
    @9
    hdmap1val0
    eqtrd
    oveq1d
    wph
    @6
    @0
    cI
    wph
    @5
    cZ
    cX
    cF
    wph
    @5
    c.0
    cZ
    c.pl
    co
    #
    cZ
    wph
    cY
    c.0
    cZ
    c.pl
    hdmap1l6b.y
    oveq1d
    wph
    cU
    cgrp
    wcel
    #
    cZ
    cV
    wcel
    @13
    cZ
    wceq
    wph
    @10
    @14
    @11
    cU
    lmodgrp
    syl
    hdmap1l6b.z
    cV
    c.pl
    cU
    cZ
    c.0
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6c.o
    grplid
    syl2anc
    eqtrd
    oteq3d
    fveq2d
    3eqtr4rd
end
