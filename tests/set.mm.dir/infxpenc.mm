include "cxp.mm"
include "ccnv.mm"
include "ccom.mm"
include "wf1o.mm"
include "com.mm"
include "coe.mm"
include "co.mm"
include "f1ocnv.mm"
include "syl.mm"
include "comu.mm"
include "c2o.mm"
include "cid.mm"
include "cres.mm"
include "f1oi.mm"
include "a1i.mm"
include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "c1o.mm"
include "cdif.mm"
include "omelon.mm"
include "2on.mm"
include "oecl.mm"
include "sylancl.mm"
include "peano1.mm"
include "oen0.mm"
include "syl21anc.mm"
include "ondif1.mm"
include "sylanbrc.mm"
include "eldifad.mm"
include "oef1o.mm"
include "omf1o.mm"
include "mpbir2an.mm"
include "omcl.mm"
include "syl2anc.mm"
include "cfv.mm"
include "wceq.mm"
include "fvresi.mm"
include "mp1i.mm"
include "wb.mm"
include "oeoe.mm"
include "syl3anc.mm"
include "f1oeq3.mm"
include "mpbird.mm"
include "f1oco.mm"
include "coa.mm"
include "csuc.mm"
include "df-2o.mm"
include "oveq2i.mm"
include "1on.mm"
include "omsuc.mm"
include "syl5eq.mm"
include "om1.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "oeoa.mm"
include "f1oeq2.mm"
include "mpbid.mm"
include "omxpenlem.mm"
include "cv.mm"
include "cop.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "wf.mm"
include "f1of.mm"
include "feqmptd.mm"
include "f1oeq1.mm"
include "xpf1o.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem infxpenc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume infxpenc.1: |- ( ph -> A e. On )
  assume infxpenc.2: |- ( ph -> _om C_ A )
  assume infxpenc.3: |- ( ph -> W e. ( On \ 1o ) )
  assume infxpenc.4: |- ( ph -> F : ( _om ^o 2o ) -1-1-onto-> _om )
  assume infxpenc.5: |- ( ph -> ( F ` (/) ) = (/) )
  assume infxpenc.6: |- ( ph -> N : A -1-1-onto-> ( _om ^o W ) )
  assume infxpenc.k: |- K = ( y e. { x e. ( ( _om ^o 2o ) ^m W ) | x finSupp (/) } |-> ( F o. ( y o. `' ( _I |` W ) ) ) )
  assume infxpenc.h: |- H = ( ( ( _om CNF W ) o. K ) o. `' ( ( _om ^o 2o ) CNF W ) )
  assume infxpenc.l: |- L = ( y e. { x e. ( _om ^m ( W .o 2o ) ) | x finSupp (/) } |-> ( ( _I |` _om ) o. ( y o. `' ( Y o. `' X ) ) ) )
  assume infxpenc.x: |- X = ( z e. 2o , w e. W |-> ( ( W .o z ) +o w ) )
  assume infxpenc.y: |- Y = ( z e. 2o , w e. W |-> ( ( 2o .o w ) +o z ) )
  assume infxpenc.j: |- J = ( ( ( _om CNF ( 2o .o W ) ) o. L ) o. `' ( _om CNF ( W .o 2o ) ) )
  assume infxpenc.z: |- Z = ( x e. ( _om ^o W ) , y e. ( _om ^o W ) |-> ( ( ( _om ^o W ) .o x ) +o y ) )
  assume infxpenc.t: |- T = ( x e. A , y e. A |-> <. ( N ` x ) , ( N ` y ) >. )
  assume infxpenc.g: |- G = ( `' N o. ( ( ( H o. J ) o. Z ) o. T ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint W w
  disjoint x z
  disjoint W x
  disjoint y z
  disjoint W y
  disjoint W z
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> G : ( A X. A ) -1-1-onto-> A )

  proof
    wph
    cA
    cA
    cxp
    #
    cA
    cN
    ccnv
    #
    cH
    cJ
    ccom
    #
    cZ
    ccom
    #
    cT
    ccom
    #
    ccom
    #
    wf1o
    #
    @0
    cA
    cG
    wf1o
    #
    wph
    com
    cW
    coe
    co
    #
    cA
    @1
    wf1o
    #
    @0
    @8
    @4
    wf1o
    #
    @6
    wph
    cA
    @8
    cN
    wf1o
    #
    @9
    infxpenc.6
    cA
    @8
    cN
    f1ocnv
    syl
    wph
    @8
    @8
    cxp
    #
    @8
    @3
    wf1o
    #
    @0
    @12
    cT
    wf1o
    #
    @10
    wph
    @8
    @8
    comu
    co
    #
    @8
    @2
    wf1o
    #
    @12
    @15
    cZ
    wf1o
    #
    @13
    wph
    com
    cW
    c2o
    comu
    co
    #
    coe
    co
    #
    @8
    @2
    wf1o
    #
    @16
    wph
    com
    c2o
    coe
    co
    #
    cW
    coe
    co
    #
    @8
    cH
    wf1o
    @19
    @22
    cJ
    wf1o
    #
    @20
    wph
    vx
    vy
    @21
    cW
    com
    cW
    cF
    cid
    cW
    cres
    #
    cH
    cK
    infxpenc.4
    cW
    cW
    @24
    wf1o
    wph
    cW
    f1oi
    a1i
    wph
    @21
    con0
    wcel
    #
    c0
    @21
    wcel
    #
    @21
    con0
    c1o
    cdif
    #
    wcel
    wph
    com
    con0
    wcel
    #
    c2o
    con0
    wcel
    #
    @25
    @28
    wph
    omelon
    a1i
    #
    2on
    com
    c2o
    oecl
    sylancl
    wph
    @28
    @29
    c0
    com
    wcel
    #
    @26
    @30
    @29
    wph
    2on
    a1i
    #
    @31
    wph
    peano1
    a1i
    com
    c2o
    oen0
    syl21anc
    @21
    ondif1
    sylanbrc
    wph
    cW
    con0
    c1o
    infxpenc.3
    eldifad
    #
    @30
    @33
    infxpenc.5
    infxpenc.k
    infxpenc.h
    oef1o
    wph
    @23
    @19
    com
    c2o
    cW
    comu
    co
    #
    coe
    co
    #
    cJ
    wf1o
    #
    wph
    vx
    vy
    com
    @18
    com
    @34
    cid
    com
    cres
    #
    cY
    cX
    ccnv
    ccom
    #
    cJ
    cL
    com
    com
    @37
    wf1o
    wph
    com
    f1oi
    a1i
    wph
    cW
    con0
    wcel
    #
    @29
    @18
    @34
    @38
    wf1o
    @33
    2on
    vz
    vw
    cW
    c2o
    cX
    cY
    infxpenc.x
    infxpenc.y
    omf1o
    sylancl
    com
    @27
    wcel
    #
    wph
    @40
    @28
    @31
    omelon
    peano1
    com
    ondif1
    mpbir2an
    a1i
    wph
    @39
    @29
    @18
    con0
    wcel
    @33
    2on
    cW
    c2o
    omcl
    sylancl
    @30
    wph
    @29
    @39
    @34
    con0
    wcel
    @32
    @33
    c2o
    cW
    omcl
    syl2anc
    @31
    c0
    @37
    cfv
    c0
    wceq
    wph
    peano1
    com
    c0
    fvresi
    mp1i
    infxpenc.l
    infxpenc.j
    oef1o
    wph
    @22
    @35
    wceq
    #
    @23
    @36
    wb
    wph
    @28
    @29
    @39
    @41
    @30
    @32
    @33
    com
    c2o
    cW
    oeoe
    syl3anc
    @22
    @35
    @19
    cJ
    f1oeq3
    syl
    mpbird
    @19
    @22
    @8
    cH
    cJ
    f1oco
    syl2anc
    wph
    @19
    @15
    wceq
    @20
    @16
    wb
    wph
    @19
    com
    cW
    cW
    coa
    co
    #
    coe
    co
    #
    @15
    wph
    @18
    @42
    com
    coe
    wph
    @18
    cW
    c1o
    comu
    co
    #
    cW
    coa
    co
    #
    @42
    wph
    @18
    cW
    c1o
    csuc
    #
    comu
    co
    #
    @45
    c2o
    @46
    cW
    comu
    df-2o
    oveq2i
    wph
    @39
    c1o
    con0
    wcel
    @47
    @45
    wceq
    @33
    1on
    cW
    c1o
    omsuc
    sylancl
    syl5eq
    wph
    @44
    cW
    cW
    coa
    wph
    @39
    @44
    cW
    wceq
    @33
    cW
    om1
    syl
    oveq1d
    eqtrd
    oveq2d
    wph
    @28
    @39
    @39
    @43
    @15
    wceq
    @30
    @33
    @33
    com
    cW
    cW
    oeoa
    syl3anc
    eqtrd
    @19
    @15
    @8
    @2
    f1oeq2
    syl
    mpbid
    wph
    @8
    con0
    wcel
    #
    @48
    @17
    wph
    @28
    @39
    @48
    @30
    @33
    com
    cW
    oecl
    syl2anc
    #
    @49
    vx
    vy
    @8
    @8
    cZ
    infxpenc.z
    omxpenlem
    syl2anc
    @12
    @15
    @8
    @2
    cZ
    f1oco
    syl2anc
    wph
    @0
    @12
    vx
    vy
    cA
    cA
    vx
    cv
    cN
    cfv
    #
    vy
    cv
    cN
    cfv
    #
    cop
    cmpt2
    #
    wf1o
    #
    @14
    wph
    vx
    vy
    cA
    @8
    cA
    @8
    @50
    @51
    wph
    @11
    cA
    @8
    vx
    cA
    @50
    cmpt
    #
    wf1o
    #
    infxpenc.6
    wph
    cN
    @54
    wceq
    @11
    @55
    wb
    wph
    vx
    cA
    @8
    cN
    wph
    @11
    cA
    @8
    cN
    wf
    infxpenc.6
    cA
    @8
    cN
    f1of
    syl
    #
    feqmptd
    cA
    @8
    cN
    @54
    f1oeq1
    syl
    mpbid
    wph
    @11
    cA
    @8
    vy
    cA
    @51
    cmpt
    #
    wf1o
    #
    infxpenc.6
    wph
    cN
    @57
    wceq
    @11
    @58
    wb
    wph
    vy
    cA
    @8
    cN
    @56
    feqmptd
    cA
    @8
    cN
    @57
    f1oeq1
    syl
    mpbid
    xpf1o
    cT
    @52
    wceq
    @14
    @53
    wb
    infxpenc.t
    @0
    @12
    cT
    @52
    f1oeq1
    ax-mp
    sylibr
    @0
    @12
    @8
    @3
    cT
    f1oco
    syl2anc
    @0
    @8
    cA
    @1
    @4
    f1oco
    syl2anc
    cG
    @5
    wceq
    @7
    @6
    wb
    infxpenc.g
    @0
    cA
    cG
    @5
    f1oeq1
    ax-mp
    sylibr
end
