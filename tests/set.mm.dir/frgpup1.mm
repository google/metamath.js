include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "wcel.mm"
include "cgrp.mm"
include "frgpgrp.mm"
include "syl.mm"
include "frgpupf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cqs.mm"
include "wss.mm"
include "cbs.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cvv.mm"
include "cqus.mm"
include "frgpval.mm"
include "cword.mm"
include "cid.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "syl5eq.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "cefg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvexd.mm"
include "qusbas.mm"
include "syl6reqr.mm"
include "eqimss.mm"
include "adantr.mm"
include "sselda.mm"
include "cec.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "adantlr.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cconcat.mm"
include "ccom.mm"
include "cgsu.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "ccatcl.mm"
include "syl2an.mm"
include "efgrcl.mm"
include "simprd.mm"
include "eleqtrrd.mm"
include "frgpupval.mm"
include "sylan2.mm"
include "wf.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "frgpuptf.mm"
include "ccatco.mm"
include "syl3anc.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "wrdco.mm"
include "syl2anr.mm"
include "adantrr.mm"
include "syl2anc.mm"
include "gsumccat.mm"
include "3eqtrd.mm"
include "frgpadd.mm"
include "adantl.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "anass1rs.mm"
include "ectocld.mm"
include "syldan.mm"
include "an32s.mm"
include "anasss.mm"
include "isghmd.mm"

theorem frgpup1
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.sm: class .~
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let vc: setvar c
  let vh: setvar h
  let vt: setvar t
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let cK: class K
  let cM: class M
  assume frgpup.b: |- B = ( Base ` H )
  assume frgpup.n: |- N = ( invg ` H )
  assume frgpup.t: |- T = ( y e. I , z e. 2o |-> if ( z = (/) , ( F ` y ) , ( N ` ( F ` y ) ) ) )
  assume frgpup.h: |- ( ph -> H e. Grp )
  assume frgpup.i: |- ( ph -> I e. V )
  assume frgpup.a: |- ( ph -> F : I --> B )
  assume frgpup.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpup.r: |- .~ = ( ~FG ` I )
  assume frgpup.g: |- G = ( freeGrp ` I )
  assume frgpup.x: |- X = ( Base ` G )
  assume frgpup.e: |- E = ran ( g e. W |-> <. [ g ] .~ , ( H gsum ( T o. g ) ) >. )

  disjoint g y
  disjoint g z
  disjoint y z
  disjoint H g
  disjoint F y
  disjoint F z
  disjoint N y
  disjoint N z
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint T g
  disjoint .~ g
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint I y
  disjoint I z
  disjoint W g
  disjoint a b
  disjoint a g
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint g u
  disjoint g v
  disjoint A g
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint a c
  disjoint a h
  disjoint a t
  disjoint E a
  disjoint c h
  disjoint c t
  disjoint c u
  disjoint E c
  disjoint h t
  disjoint h u
  disjoint E h
  disjoint t u
  disjoint E t
  disjoint E u
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint H a
  disjoint b c
  disjoint b h
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint H b
  disjoint c g
  disjoint c n
  disjoint c r
  disjoint c v
  disjoint c x
  disjoint H c
  disjoint g h
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint g x
  disjoint h n
  disjoint h r
  disjoint h v
  disjoint h x
  disjoint H h
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint H n
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint H r
  disjoint t v
  disjoint t x
  disjoint H t
  disjoint u x
  disjoint H u
  disjoint v x
  disjoint H v
  disjoint H x
  disjoint C u
  disjoint C v
  disjoint a i
  disjoint a j
  disjoint a w
  disjoint K a
  disjoint i j
  disjoint i n
  disjoint i t
  disjoint i w
  disjoint K i
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint K j
  disjoint n w
  disjoint K n
  disjoint t w
  disjoint K t
  disjoint K w
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint B a
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint G a
  disjoint c w
  disjoint G c
  disjoint G t
  disjoint u w
  disjoint G u
  disjoint G w
  disjoint T a
  disjoint b i
  disjoint b j
  disjoint T b
  disjoint g i
  disjoint g j
  disjoint h i
  disjoint h j
  disjoint T h
  disjoint i r
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint T i
  disjoint j r
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint T j
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint .~ a
  disjoint b w
  disjoint .~ b
  disjoint g w
  disjoint h w
  disjoint .~ h
  disjoint .~ i
  disjoint .~ j
  disjoint .~ n
  disjoint r w
  disjoint .~ r
  disjoint .~ t
  disjoint .~ u
  disjoint w x
  disjoint .~ w
  disjoint .~ x
  disjoint a ph
  disjoint b ph
  disjoint c i
  disjoint c j
  disjoint c ph
  disjoint h ph
  disjoint i y
  disjoint i z
  disjoint i ph
  disjoint j y
  disjoint j z
  disjoint j ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint I a
  disjoint I b
  disjoint I i
  disjoint I j
  disjoint I n
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint I w
  disjoint I x
  disjoint V w
  disjoint W a
  disjoint W b
  disjoint W h
  disjoint W n
  disjoint W r
  disjoint W t
  disjoint W u
  disjoint v w
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X n
  disjoint X u
  disjoint X w
  assert |- ( ph -> E e. ( G GrpHom H ) )

  proof
    wph
    va
    vc
    cG
    cplusg
    cfv
    #
    cH
    cplusg
    cfv
    #
    cG
    cH
    cE
    cX
    cB
    frgpup.x
    frgpup.b
    @0
    eqid
    #
    @1
    eqid
    #
    wph
    cI
    cV
    wcel
    #
    cG
    cgrp
    wcel
    frgpup.i
    cG
    cI
    cV
    frgpup.g
    frgpgrp
    syl
    frgpup.h
    wph
    vy
    vz
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpupf
    wph
    va
    cv
    #
    cX
    wcel
    #
    vc
    cv
    #
    cX
    wcel
    #
    @5
    @7
    @0
    co
    #
    cE
    cfv
    #
    @5
    cE
    cfv
    #
    @7
    cE
    cfv
    #
    @1
    co
    #
    wceq
    #
    wph
    @6
    wa
    #
    @8
    @7
    cW
    c.sm
    cqs
    #
    wcel
    @14
    @15
    cX
    @16
    @7
    wph
    cX
    @16
    wss
    #
    @6
    wph
    cX
    @16
    wceq
    @17
    wph
    @16
    cG
    cbs
    cfv
    cX
    wph
    c.sm
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    cG
    cW
    cvv
    cvv
    wph
    @4
    cG
    @19
    c.sm
    cqus
    co
    wceq
    frgpup.i
    c.sm
    cG
    cI
    @19
    cV
    frgpup.g
    @19
    eqid
    #
    frgpup.r
    frgpval
    syl
    wph
    cW
    @18
    cword
    #
    @19
    cbs
    cfv
    #
    wph
    cW
    @21
    cid
    cfv
    #
    @21
    frgpup.w
    wph
    @18
    cvv
    wcel
    #
    @21
    cvv
    wcel
    @23
    @21
    wceq
    wph
    @4
    c2o
    con0
    wcel
    @24
    frgpup.i
    2on
    cI
    c2o
    cV
    con0
    xpexg
    sylancl
    #
    @18
    cvv
    wrdexg
    @21
    cvv
    fvi
    3syl
    syl5eq
    wph
    @24
    @22
    @21
    wceq
    @25
    @22
    @18
    @19
    cvv
    @20
    @22
    eqid
    frmdbas
    syl
    eqtr4d
    c.sm
    cvv
    wcel
    wph
    c.sm
    cI
    cefg
    cfv
    cvv
    frgpup.r
    cI
    cefg
    fvex
    eqeltri
    a1i
    wph
    @18
    cfrmd
    fvexd
    qusbas
    frgpup.x
    syl6reqr
    cX
    @16
    eqimss
    syl
    #
    adantr
    sselda
    @5
    vu
    cv
    #
    c.sm
    cec
    #
    @0
    co
    #
    cE
    cfv
    #
    @11
    @28
    cE
    cfv
    #
    @1
    co
    #
    wceq
    #
    @14
    @15
    vu
    @7
    cW
    c.sm
    @16
    @16
    eqid
    #
    @28
    @7
    wceq
    #
    @30
    @10
    @32
    @13
    @35
    @29
    @9
    cE
    @28
    @7
    @5
    @0
    oveq2
    fveq2d
    @35
    @31
    @12
    @11
    @1
    @28
    @7
    cE
    fveq2
    oveq2d
    eqeq12d
    wph
    @27
    cW
    wcel
    #
    @6
    @33
    wph
    @36
    wa
    #
    @6
    @5
    @16
    wcel
    #
    @33
    wph
    @6
    @38
    @36
    wph
    cX
    @16
    @5
    @26
    sselda
    adantlr
    vt
    cv
    #
    c.sm
    cec
    #
    @28
    @0
    co
    #
    cE
    cfv
    #
    @40
    cE
    cfv
    #
    @31
    @1
    co
    #
    wceq
    #
    @33
    @37
    vt
    @5
    cW
    c.sm
    @16
    @34
    @40
    @5
    wceq
    #
    @42
    @30
    @44
    @32
    @46
    @41
    @29
    cE
    @40
    @5
    @28
    @0
    oveq1
    fveq2d
    @46
    @43
    @11
    @31
    @1
    @40
    @5
    cE
    fveq2
    oveq1d
    eqeq12d
    wph
    @39
    cW
    wcel
    #
    @36
    @45
    wph
    @47
    @36
    wa
    #
    wa
    #
    @39
    @27
    cconcat
    co
    #
    c.sm
    cec
    #
    cE
    cfv
    #
    cH
    cT
    @39
    ccom
    #
    cgsu
    co
    #
    cH
    cT
    @27
    ccom
    #
    cgsu
    co
    #
    @1
    co
    #
    @42
    @44
    @49
    @52
    cH
    cT
    @50
    ccom
    #
    cgsu
    co
    #
    cH
    @53
    @55
    cconcat
    co
    #
    cgsu
    co
    #
    @57
    @48
    wph
    @50
    cW
    wcel
    @52
    @59
    wceq
    @48
    @50
    @21
    cW
    @47
    @39
    @21
    wcel
    #
    @27
    @21
    wcel
    #
    @50
    @21
    wcel
    @36
    cW
    @21
    @39
    cW
    @23
    @21
    frgpup.w
    @21
    fviss
    eqsstri
    #
    sseli
    #
    cW
    @21
    @27
    @64
    sseli
    #
    @18
    @39
    @27
    ccatcl
    syl2an
    @48
    cI
    cvv
    wcel
    #
    cW
    @21
    wceq
    #
    @47
    @67
    @68
    wa
    @36
    @39
    cI
    cW
    frgpup.w
    efgrcl
    adantr
    simprd
    eleqtrrd
    wph
    vy
    vz
    @50
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpupval
    sylan2
    @49
    @58
    @60
    cH
    cgsu
    @49
    @62
    @63
    @18
    cB
    cT
    wf
    #
    @58
    @60
    wceq
    @47
    @62
    wph
    @36
    @65
    ad2antrl
    @36
    @63
    wph
    @47
    @66
    ad2antll
    #
    wph
    @69
    @48
    wph
    vy
    vz
    cB
    cT
    cF
    cH
    cI
    cN
    cV
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpuptf
    #
    adantr
    #
    @18
    cB
    @39
    @27
    cT
    ccatco
    syl3anc
    oveq2d
    @49
    cH
    cmnd
    wcel
    #
    @53
    cB
    cword
    #
    wcel
    #
    @55
    @74
    wcel
    #
    @61
    @57
    wceq
    wph
    @73
    @48
    wph
    cH
    cgrp
    wcel
    @73
    frgpup.h
    cH
    grpmnd
    syl
    adantr
    wph
    @47
    @75
    @36
    @47
    @62
    @69
    @75
    wph
    @65
    @71
    @18
    cB
    cT
    @39
    wrdco
    syl2anr
    adantrr
    @49
    @63
    @69
    @76
    @70
    @72
    @18
    cB
    cT
    @27
    wrdco
    syl2anc
    cB
    @1
    cH
    @53
    @55
    frgpup.b
    @3
    gsumccat
    syl3anc
    3eqtrd
    @49
    @41
    @51
    cE
    @48
    @41
    @51
    wceq
    wph
    @39
    @27
    @0
    c.sm
    cG
    cI
    cW
    frgpup.w
    frgpup.g
    frgpup.r
    @2
    frgpadd
    adantl
    fveq2d
    @49
    @43
    @54
    @31
    @56
    @1
    wph
    @47
    @43
    @54
    wceq
    @36
    wph
    vy
    vz
    @39
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpupval
    adantrr
    wph
    @36
    @31
    @56
    wceq
    @47
    wph
    vy
    vz
    @27
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpupval
    adantrl
    oveq12d
    3eqtr4d
    anass1rs
    ectocld
    syldan
    an32s
    ectocld
    syldan
    anasss
    isghmd
end
