include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "coe1mul.mm"
include "wa.mm"
include "eqeq2.mm"
include "cvv.mm"
include "cmnd.mm"
include "ad2antrr.mm"
include "ringmnd.mm"
include "syl.mm"
include "ovexd.mm"
include "simpr.mm"
include "wb.mm"
include "fznn0.mm"
include "ad2antlr.mm"
include "mpbir2and.mm"
include "wf.mm"
include "eqid.mm"
include "coe1f.mm"
include "adantr.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fznn0sub.mm"
include "ringcl.mm"
include "fmptd.mm"
include "csn.mm"
include "cdif.mm"
include "ad3antrrr.mm"
include "eldifi.mm"
include "adantl.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "coe1tmfv2.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "sylan2.mm"
include "adantlr.mm"
include "eqtrd.mm"
include "suppss2.mm"
include "gsumpt.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "coe1tmfv1.mm"
include "wn.mm"
include "elfzle2.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "imp.mm"
include "an32s.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "gsumz.mm"
include "ifbothda.mm"

theorem coe1tmmul
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let c.ex: class .^
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let cF: class F
  let cY: class Y
  assume coe1tm.z: |- .0. = ( 0g ` R )
  assume coe1tm.k: |- K = ( Base ` R )
  assume coe1tm.p: |- P = ( Poly1 ` R )
  assume coe1tm.x: |- X = ( var1 ` R )
  assume coe1tm.m: |- .x. = ( .s ` P )
  assume coe1tm.n: |- N = ( mulGrp ` P )
  assume coe1tm.e: |- .^ = ( .g ` N )
  assume coe1tmmul.b: |- B = ( Base ` P )
  assume coe1tmmul.t: |- .xb = ( .r ` P )
  assume coe1tmmul.u: |- .X. = ( .r ` R )
  assume coe1tmmul.a: |- ( ph -> A e. B )
  assume coe1tmmul.r: |- ( ph -> R e. Ring )
  assume coe1tmmul.c: |- ( ph -> C e. K )
  assume coe1tmmul.d: |- ( ph -> D e. NN0 )

  disjoint .0. x
  disjoint C x
  disjoint D x
  disjoint K x
  disjoint .^ x
  disjoint A x
  disjoint N x
  disjoint P x
  disjoint X x
  disjoint ph x
  disjoint R x
  disjoint .x. x
  disjoint .X. x
  disjoint .xb x
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint .0. a
  disjoint b x
  disjoint b y
  disjoint .0. b
  disjoint x y
  disjoint .0. y
  disjoint C b
  disjoint C y
  disjoint D a
  disjoint D b
  disjoint D y
  disjoint F x
  disjoint K b
  disjoint K y
  disjoint .^ y
  disjoint A y
  disjoint N y
  disjoint P y
  disjoint X y
  disjoint Y x
  disjoint ph y
  disjoint R a
  disjoint R b
  disjoint R y
  disjoint .x. y
  disjoint .X. y
  assert |- ( ph -> ( coe1 ` ( ( C .x. ( D .^ X ) ) .xb A ) ) = ( x e. NN0 |-> if ( D <_ x , ( C .X. ( ( coe1 ` A ) ` ( x - D ) ) ) , .0. ) ) )

  proof
    wph
    cC
    cD
    cX
    c.ex
    co
    c.x
    co
    #
    cA
    c.xb
    co
    cco1
    cfv
    #
    vx
    cn0
    cR
    vy
    cc0
    vx
    cv
    #
    cfz
    co
    #
    vy
    cv
    #
    @0
    cco1
    cfv
    #
    cfv
    #
    @2
    @4
    cmin
    co
    #
    cA
    cco1
    cfv
    #
    cfv
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    vx
    cn0
    cD
    @2
    cle
    wbr
    #
    cC
    @2
    cD
    cmin
    co
    #
    @8
    cfv
    #
    c.xp
    co
    #
    c.0
    cif
    #
    cmpt
    wph
    cR
    crg
    wcel
    #
    @0
    cB
    wcel
    #
    cA
    cB
    wcel
    #
    @1
    @13
    wceq
    coe1tmmul.r
    wph
    @19
    cC
    cK
    wcel
    #
    cD
    cn0
    wcel
    #
    @20
    coe1tmmul.r
    coe1tmmul.c
    coe1tmmul.d
    cB
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    coe1tmmul.b
    ply1tmcl
    syl3anc
    #
    coe1tmmul.a
    vy
    cB
    cR
    c.xb
    c.xp
    vx
    @0
    cA
    cP
    coe1tm.p
    coe1tmmul.t
    coe1tmmul.u
    coe1tmmul.b
    coe1mul
    syl3anc
    wph
    vx
    cn0
    @12
    @18
    @14
    @12
    @17
    wceq
    @12
    c.0
    wceq
    @12
    @18
    wceq
    wph
    @2
    cn0
    wcel
    #
    wa
    #
    @17
    c.0
    @17
    @18
    @12
    eqeq2
    c.0
    @18
    @12
    eqeq2
    @26
    @14
    wa
    #
    @12
    cD
    @11
    cfv
    #
    @17
    @27
    @3
    cK
    @11
    cR
    cvv
    cD
    c.0
    coe1tm.k
    coe1tm.z
    @27
    @19
    cR
    cmnd
    wcel
    #
    wph
    @19
    @25
    @14
    coe1tmmul.r
    ad2antrr
    cR
    ringmnd
    #
    syl
    @27
    cc0
    @2
    cfz
    ovexd
    #
    @27
    cD
    @3
    wcel
    #
    @23
    @14
    wph
    @23
    @25
    @14
    coe1tmmul.d
    ad2antrr
    @26
    @14
    simpr
    @25
    @32
    @23
    @14
    wa
    wb
    wph
    @14
    cD
    @2
    fznn0
    ad2antlr
    mpbir2and
    #
    @26
    @3
    cK
    @11
    wf
    @14
    @26
    vy
    @3
    @10
    cK
    @11
    @26
    @4
    @3
    wcel
    #
    wa
    #
    @19
    @6
    cK
    wcel
    #
    @9
    cK
    wcel
    #
    @10
    cK
    wcel
    wph
    @19
    @25
    @34
    coe1tmmul.r
    ad2antrr
    #
    @26
    cn0
    cK
    @5
    wf
    #
    @4
    cn0
    wcel
    #
    @36
    @34
    wph
    @39
    @25
    wph
    @20
    @39
    @24
    @5
    cB
    cP
    cR
    @0
    cK
    @5
    eqid
    coe1tmmul.b
    coe1tm.p
    coe1tm.k
    coe1f
    syl
    adantr
    @4
    @2
    elfznn0
    #
    cn0
    cK
    @4
    @5
    ffvelrn
    syl2an
    @26
    cn0
    cK
    @8
    wf
    #
    @7
    cn0
    wcel
    @37
    @34
    wph
    @42
    @25
    wph
    @21
    @42
    coe1tmmul.a
    @8
    cB
    cP
    cR
    cA
    cK
    @8
    eqid
    coe1tmmul.b
    coe1tm.p
    coe1tm.k
    coe1f
    syl
    adantr
    @4
    cc0
    @2
    fznn0sub
    cn0
    cK
    @7
    @8
    ffvelrn
    syl2an
    #
    cK
    cR
    c.xp
    @6
    @9
    coe1tm.k
    coe1tmmul.u
    ringcl
    syl3anc
    @11
    eqid
    #
    fmptd
    adantr
    @27
    @3
    @10
    vy
    cvv
    cD
    csn
    #
    c.0
    @27
    @4
    @3
    @45
    cdif
    wcel
    #
    wa
    #
    @10
    c.0
    @9
    c.xp
    co
    #
    c.0
    @47
    @6
    c.0
    @9
    c.xp
    @47
    cC
    cD
    cP
    cR
    c.x
    c.ex
    @4
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    wph
    @19
    @25
    @14
    @46
    coe1tmmul.r
    ad3antrrr
    wph
    @22
    @25
    @14
    @46
    coe1tmmul.c
    ad3antrrr
    wph
    @23
    @25
    @14
    @46
    coe1tmmul.d
    ad3antrrr
    @46
    @40
    @27
    @46
    @34
    @40
    @4
    @3
    @45
    eldifi
    #
    @41
    syl
    adantl
    @46
    cD
    @4
    wne
    #
    @27
    @46
    @4
    cD
    @4
    @3
    cD
    eldifsni
    necomd
    adantl
    coe1tmfv2
    oveq1d
    @26
    @46
    @48
    c.0
    wceq
    #
    @14
    @46
    @26
    @34
    @51
    @49
    @35
    @19
    @37
    @51
    @38
    @43
    cK
    cR
    c.xp
    @9
    c.0
    coe1tm.k
    coe1tmmul.u
    coe1tm.z
    ringlz
    syl2anc
    #
    sylan2
    adantlr
    eqtrd
    @31
    suppss2
    gsumpt
    @27
    @28
    cD
    @5
    cfv
    #
    @16
    c.xp
    co
    #
    @17
    @27
    @32
    @28
    @54
    wceq
    @33
    vy
    cD
    @10
    @54
    @3
    @11
    @4
    cD
    wceq
    #
    @6
    @53
    @9
    @16
    c.xp
    @4
    cD
    @5
    fveq2
    @55
    @7
    @15
    @8
    @4
    cD
    @2
    cmin
    oveq2
    fveq2d
    oveq12d
    @44
    @53
    @16
    c.xp
    ovex
    fvmpt
    syl
    @27
    @53
    cC
    @16
    c.xp
    wph
    @53
    cC
    wceq
    #
    @25
    @14
    wph
    @19
    @22
    @23
    @56
    coe1tmmul.r
    coe1tmmul.c
    coe1tmmul.d
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    coe1tmfv1
    syl3anc
    ad2antrr
    oveq1d
    eqtrd
    eqtrd
    @26
    @14
    wn
    #
    wa
    #
    @12
    cR
    vy
    @3
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @58
    @11
    @59
    cR
    cgsu
    @58
    vy
    @3
    @10
    c.0
    @58
    @34
    wa
    #
    @10
    @48
    c.0
    @61
    @6
    c.0
    @9
    c.xp
    @61
    cC
    cD
    cP
    cR
    c.x
    c.ex
    @4
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    wph
    @19
    @25
    @57
    @34
    coe1tmmul.r
    ad3antrrr
    wph
    @22
    @25
    @57
    @34
    coe1tmmul.c
    ad3antrrr
    wph
    @23
    @25
    @57
    @34
    coe1tmmul.d
    ad3antrrr
    @34
    @40
    @58
    @41
    adantl
    @26
    @34
    @57
    @50
    @35
    @57
    @50
    @35
    @14
    cD
    @4
    @35
    @14
    cD
    @4
    wceq
    @4
    @2
    cle
    wbr
    #
    @34
    @62
    @26
    @4
    cc0
    @2
    elfzle2
    adantl
    cD
    @4
    @2
    cle
    breq1
    syl5ibrcom
    necon3bd
    imp
    an32s
    coe1tmfv2
    oveq1d
    @26
    @34
    @51
    @57
    @52
    adantlr
    eqtrd
    mpteq2dva
    oveq2d
    @58
    @29
    @3
    cvv
    wcel
    @60
    c.0
    wceq
    wph
    @29
    @25
    @57
    wph
    @19
    @29
    coe1tmmul.r
    @30
    syl
    ad2antrr
    @58
    cc0
    @2
    cfz
    ovexd
    @3
    vy
    cR
    cvv
    c.0
    coe1tm.z
    gsumz
    syl2anc
    eqtrd
    ifbothda
    mpteq2dva
    eqtrd
end
