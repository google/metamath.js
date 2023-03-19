include "cfv.mm"
include "cotp.mm"
include "wceq.mm"
include "csn.mm"
include "csg.mm"
include "co.mm"
include "wa.mm"
include "eqid.mm"
include "eldifad.mm"
include "hdmap1cl.mm"
include "eqeltrrd.mm"
include "hdmap1eq.mm"
include "mpbid.mm"
include "simpld.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lspsnneg.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "lcdlmod.mm"
include "3eqtr4d.mm"
include "simprd.mm"
include "cabl.mm"
include "lmodabl.mm"
include "syl.mm"
include "ablsub2inv.mm"
include "sneqd.mm"
include "lspsnsub.mm"
include "eqtrd.mm"
include "cgrp.mm"
include "cdif.mm"
include "lmodgrp.mm"
include "grpinvnzcl.mm"
include "lmodvnegcl.mm"
include "3netr4d.mm"
include "mpbir2and.mm"

theorem hdmap1neglem1N
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmap1neglem1.h: |- H = ( LHyp ` K )
  assume hdmap1neglem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1neglem1.v: |- V = ( Base ` U )
  assume hdmap1neglem1.r: |- R = ( invg ` U )
  assume hdmap1neglem1.o: |- .0. = ( 0g ` U )
  assume hdmap1neglem1.n: |- N = ( LSpan ` U )
  assume hdmap1neglem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1neglem1.d: |- D = ( Base ` C )
  assume hdmap1neglem1.s: |- S = ( invg ` C )
  assume hdmap1neglem1.l: |- L = ( LSpan ` C )
  assume hdmap1neglem1.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1neglem1.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1neglem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1neglem1.f: |- ( ph -> F e. D )
  assume hdmap1neglem1.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1neglem1.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume hdmap1neglem1.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1neglem1.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1neglem1.e: |- ( ph -> ( I ` <. X , F , Y >. ) = G )


  assert |- ( ph -> ( I ` <. ( R ` X ) , ( S ` F ) , ( R ` Y ) >. ) = ( S ` G ) )

  proof
    wph
    cX
    cR
    cfv
    #
    cF
    cS
    cfv
    #
    cY
    cR
    cfv
    #
    cotp
    cI
    cfv
    cG
    cS
    cfv
    #
    wceq
    @2
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    @3
    csn
    cL
    cfv
    #
    wceq
    @0
    @2
    cU
    csg
    cfv
    #
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @1
    @3
    cC
    csg
    cfv
    #
    co
    #
    csn
    #
    cL
    cfv
    #
    wceq
    wph
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cG
    csn
    cL
    cfv
    #
    @5
    @6
    wph
    @17
    @18
    wceq
    #
    cX
    cY
    @7
    co
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    cF
    cG
    @12
    co
    csn
    cL
    cfv
    #
    wceq
    #
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cG
    wceq
    @19
    @23
    wa
    hdmap1neglem1.e
    wph
    cC
    cD
    @12
    cU
    cF
    cG
    cH
    cI
    cK
    cL
    cM
    @7
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1neglem1.h
    hdmap1neglem1.u
    hdmap1neglem1.v
    @7
    eqid
    #
    hdmap1neglem1.o
    hdmap1neglem1.n
    hdmap1neglem1.c
    hdmap1neglem1.d
    @12
    eqid
    #
    hdmap1neglem1.l
    hdmap1neglem1.m
    hdmap1neglem1.i
    hdmap1neglem1.k
    hdmap1neglem1.x
    hdmap1neglem1.f
    hdmap1neglem1.y
    wph
    @24
    cG
    cD
    hdmap1neglem1.e
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
    cY
    c.0
    hdmap1neglem1.h
    hdmap1neglem1.u
    hdmap1neglem1.v
    hdmap1neglem1.o
    hdmap1neglem1.n
    hdmap1neglem1.c
    hdmap1neglem1.d
    hdmap1neglem1.l
    hdmap1neglem1.m
    hdmap1neglem1.i
    hdmap1neglem1.k
    hdmap1neglem1.f
    hdmap1neglem1.mn
    hdmap1neglem1.ne
    hdmap1neglem1.x
    wph
    cY
    cV
    c.0
    csn
    #
    hdmap1neglem1.y
    eldifad
    #
    hdmap1cl
    eqeltrrd
    #
    hdmap1neglem1.ne
    hdmap1neglem1.mn
    hdmap1eq
    mpbid
    #
    simpld
    wph
    @4
    @16
    cM
    wph
    cU
    clmod
    wcel
    #
    cY
    cV
    wcel
    @4
    @16
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmap1neglem1.h
    hdmap1neglem1.u
    hdmap1neglem1.k
    dvhlmod
    #
    @28
    cR
    cN
    cV
    cU
    cY
    hdmap1neglem1.v
    hdmap1neglem1.r
    hdmap1neglem1.n
    lspsnneg
    syl2anc
    #
    fveq2d
    wph
    cC
    clmod
    wcel
    #
    cG
    cD
    wcel
    #
    @6
    @18
    wceq
    wph
    cC
    cH
    cK
    cW
    hdmap1neglem1.h
    hdmap1neglem1.c
    hdmap1neglem1.k
    lcdlmod
    #
    @29
    cS
    cL
    cD
    cC
    cG
    hdmap1neglem1.d
    hdmap1neglem1.s
    hdmap1neglem1.l
    lspsnneg
    syl2anc
    3eqtr4d
    wph
    @21
    @22
    @11
    @15
    wph
    @19
    @23
    @30
    simprd
    wph
    @10
    @20
    cM
    wph
    @10
    cY
    cX
    @7
    co
    #
    csn
    #
    cN
    cfv
    @20
    wph
    @9
    @38
    cN
    wph
    @8
    @37
    wph
    cV
    cU
    @7
    cR
    cX
    cY
    hdmap1neglem1.v
    @25
    hdmap1neglem1.r
    wph
    @31
    cU
    cabl
    wcel
    @32
    cU
    lmodabl
    syl
    wph
    cX
    cV
    @27
    hdmap1neglem1.x
    eldifad
    #
    @28
    ablsub2inv
    sneqd
    fveq2d
    wph
    @7
    cN
    cV
    cU
    cY
    cX
    hdmap1neglem1.v
    @25
    hdmap1neglem1.n
    @32
    @28
    @39
    lspsnsub
    eqtrd
    fveq2d
    wph
    @15
    cG
    cF
    @12
    co
    #
    csn
    #
    cL
    cfv
    @22
    wph
    @14
    @41
    cL
    wph
    @13
    @40
    wph
    cD
    cC
    @12
    cS
    cF
    cG
    hdmap1neglem1.d
    @26
    hdmap1neglem1.s
    wph
    @34
    cC
    cabl
    wcel
    @36
    cC
    lmodabl
    syl
    hdmap1neglem1.f
    @29
    ablsub2inv
    sneqd
    fveq2d
    wph
    @12
    cL
    cD
    cC
    cG
    cF
    hdmap1neglem1.d
    @26
    hdmap1neglem1.l
    @36
    @29
    hdmap1neglem1.f
    lspsnsub
    eqtrd
    3eqtr4d
    wph
    cC
    cD
    @12
    cU
    @1
    @3
    cH
    cI
    cK
    cL
    cM
    @7
    cN
    cV
    cW
    @0
    @2
    c.0
    hdmap1neglem1.h
    hdmap1neglem1.u
    hdmap1neglem1.v
    @25
    hdmap1neglem1.o
    hdmap1neglem1.n
    hdmap1neglem1.c
    hdmap1neglem1.d
    @26
    hdmap1neglem1.l
    hdmap1neglem1.m
    hdmap1neglem1.i
    hdmap1neglem1.k
    wph
    cU
    cgrp
    wcel
    #
    cX
    cV
    @27
    cdif
    #
    wcel
    @0
    @43
    wcel
    wph
    @31
    @42
    @32
    cU
    lmodgrp
    syl
    #
    hdmap1neglem1.x
    cV
    cU
    cR
    cX
    c.0
    hdmap1neglem1.v
    hdmap1neglem1.o
    hdmap1neglem1.r
    grpinvnzcl
    syl2anc
    wph
    @34
    cF
    cD
    wcel
    #
    @1
    cD
    wcel
    @36
    hdmap1neglem1.f
    cS
    cD
    cC
    cF
    hdmap1neglem1.d
    hdmap1neglem1.s
    lmodvnegcl
    syl2anc
    wph
    @42
    cY
    @43
    wcel
    @2
    @43
    wcel
    @44
    hdmap1neglem1.y
    cV
    cU
    cR
    cY
    c.0
    hdmap1neglem1.v
    hdmap1neglem1.o
    hdmap1neglem1.r
    grpinvnzcl
    syl2anc
    wph
    @34
    @35
    @3
    cD
    wcel
    @36
    @29
    cS
    cD
    cC
    cG
    hdmap1neglem1.d
    hdmap1neglem1.s
    lmodvnegcl
    syl2anc
    wph
    cX
    csn
    cN
    cfv
    #
    @16
    @0
    csn
    cN
    cfv
    #
    @4
    hdmap1neglem1.ne
    wph
    @31
    cX
    cV
    wcel
    @47
    @46
    wceq
    @32
    @39
    cR
    cN
    cV
    cU
    cX
    hdmap1neglem1.v
    hdmap1neglem1.r
    hdmap1neglem1.n
    lspsnneg
    syl2anc
    #
    @33
    3netr4d
    wph
    @46
    cM
    cfv
    cF
    csn
    cL
    cfv
    #
    @47
    cM
    cfv
    @1
    csn
    cL
    cfv
    #
    hdmap1neglem1.mn
    wph
    @47
    @46
    cM
    @48
    fveq2d
    wph
    @34
    @45
    @50
    @49
    wceq
    @36
    hdmap1neglem1.f
    cS
    cL
    cD
    cC
    cF
    hdmap1neglem1.d
    hdmap1neglem1.s
    hdmap1neglem1.l
    lspsnneg
    syl2anc
    3eqtr4d
    hdmap1eq
    mpbir2and
end
