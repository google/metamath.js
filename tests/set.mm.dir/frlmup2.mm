include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "wcel.mm"
include "wceq.mm"
include "crg.mm"
include "wf.mm"
include "csca.mm"
include "clmod.mm"
include "eqid.mm"
include "lmodring.mm"
include "syl.mm"
include "eqeltrd.mm"
include "uvcff.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "cv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "c0g.mm"
include "ccmn.mm"
include "cmnd.mm"
include "lmodcmn.mm"
include "cmnmnd.mm"
include "3syl.mm"
include "cbs.mm"
include "frlmbasf.mm"
include "fveq2d.mm"
include "feq3d.mm"
include "mpbid.mm"
include "lcomf.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "uvcvv0.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "lmod0vs.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "gsumpt.mm"
include "cur.mm"
include "uvcvv1.mm"
include "lmodvs1.mm"

theorem frlmup2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cI: class I
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cK: class K
  assume frlmup.f: |- F = ( R freeLMod I )
  assume frlmup.b: |- B = ( Base ` F )
  assume frlmup.c: |- C = ( Base ` T )
  assume frlmup.v: |- .x. = ( .s ` T )
  assume frlmup.e: |- E = ( x e. B |-> ( T gsum ( x oF .x. A ) ) )
  assume frlmup.t: |- ( ph -> T e. LMod )
  assume frlmup.i: |- ( ph -> I e. X )
  assume frlmup.r: |- ( ph -> R = ( Scalar ` T ) )
  assume frlmup.a: |- ( ph -> A : I --> C )
  assume frlmup.y: |- ( ph -> Y e. I )
  assume frlmup.u: |- U = ( R unitVec I )

  disjoint R x
  disjoint I x
  disjoint F x
  disjoint B x
  disjoint C x
  disjoint .x. x
  disjoint A x
  disjoint X x
  disjoint ph x
  disjoint Y x
  disjoint U x
  disjoint T x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint I y
  disjoint I z
  disjoint I w
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint X y
  disjoint X z
  disjoint X w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint Y y
  disjoint Y z
  disjoint Y w
  disjoint U y
  disjoint U z
  disjoint U w
  disjoint T y
  disjoint T z
  disjoint T w
  assert |- ( ph -> ( E ` ( U ` Y ) ) = ( A ` Y ) )

  proof
    wph
    cY
    cU
    cfv
    #
    cE
    cfv
    #
    cT
    @0
    cA
    c.x
    cof
    #
    co
    #
    cgsu
    co
    #
    cY
    @3
    cfv
    #
    cY
    cA
    cfv
    #
    wph
    @0
    cB
    wcel
    #
    @1
    @4
    wceq
    wph
    cI
    cB
    cY
    cU
    wph
    cR
    crg
    wcel
    #
    cI
    cX
    wcel
    #
    cI
    cB
    cU
    wf
    wph
    cR
    cT
    csca
    cfv
    #
    crg
    frlmup.r
    wph
    cT
    clmod
    wcel
    #
    @10
    crg
    wcel
    frlmup.t
    @10
    cT
    @10
    eqid
    #
    lmodring
    syl
    eqeltrd
    #
    frlmup.i
    cB
    cR
    cU
    cI
    cX
    cF
    frlmup.u
    frlmup.f
    frlmup.b
    uvcff
    syl2anc
    frlmup.y
    ffvelrnd
    #
    vx
    @0
    cT
    vx
    cv
    #
    cA
    @2
    co
    #
    cgsu
    co
    @4
    cB
    cE
    @15
    @0
    wceq
    @16
    @3
    cT
    cgsu
    @15
    @0
    cA
    @2
    oveq1
    oveq2d
    frlmup.e
    cT
    @3
    cgsu
    ovex
    fvmpt
    syl
    wph
    cI
    cC
    @3
    cT
    cX
    cY
    cT
    c0g
    cfv
    #
    frlmup.c
    @17
    eqid
    #
    wph
    @11
    cT
    ccmn
    wcel
    cT
    cmnd
    wcel
    frlmup.t
    cT
    lmodcmn
    cT
    cmnmnd
    3syl
    frlmup.i
    frlmup.y
    wph
    cC
    c.x
    @10
    @0
    cA
    cI
    @10
    cbs
    cfv
    #
    cX
    cT
    @12
    @19
    eqid
    frlmup.v
    frlmup.c
    frlmup.t
    wph
    cI
    cR
    cbs
    cfv
    #
    @0
    wf
    #
    cI
    @19
    @0
    wf
    wph
    @9
    @7
    @21
    frlmup.i
    @14
    cB
    cR
    cF
    cI
    @20
    cX
    @0
    frlmup.f
    @20
    eqid
    frlmup.b
    frlmbasf
    syl2anc
    #
    wph
    @20
    @19
    @0
    cI
    wph
    cR
    @10
    cbs
    frlmup.r
    fveq2d
    feq3d
    mpbid
    frlmup.a
    frlmup.i
    lcomf
    #
    wph
    cI
    cC
    vx
    @3
    cY
    csn
    #
    @17
    @23
    wph
    @15
    cI
    @24
    cdif
    wcel
    #
    wa
    #
    @15
    @3
    cfv
    #
    @15
    @0
    cfv
    #
    @15
    cA
    cfv
    #
    c.x
    co
    #
    @10
    c0g
    cfv
    #
    @29
    c.x
    co
    #
    @17
    @26
    @0
    cI
    wfn
    #
    cA
    cI
    wfn
    #
    @9
    @15
    cI
    wcel
    #
    @27
    @30
    wceq
    wph
    @33
    @25
    wph
    @21
    @33
    @22
    cI
    @20
    @0
    ffn
    syl
    #
    adantr
    wph
    @34
    @25
    wph
    cI
    cC
    cA
    wf
    #
    @34
    frlmup.a
    cI
    cC
    cA
    ffn
    syl
    #
    adantr
    wph
    @9
    @25
    frlmup.i
    adantr
    #
    @25
    @35
    wph
    @15
    cI
    @24
    eldifi
    #
    adantl
    #
    cI
    c.x
    @0
    cA
    cX
    @15
    fnfvof
    syl22anc
    @26
    @28
    @31
    @29
    c.x
    @26
    @28
    cR
    c0g
    cfv
    #
    @31
    @26
    cR
    cU
    cI
    cY
    @15
    crg
    cX
    @42
    frlmup.u
    wph
    @8
    @25
    @13
    adantr
    @39
    wph
    cY
    cI
    wcel
    #
    @25
    frlmup.y
    adantr
    @41
    @25
    cY
    @15
    wne
    wph
    @25
    @15
    cY
    @15
    cI
    cY
    eldifsni
    necomd
    adantl
    @42
    eqid
    uvcvv0
    wph
    @42
    @31
    wceq
    @25
    wph
    cR
    @10
    c0g
    frlmup.r
    fveq2d
    adantr
    eqtrd
    oveq1d
    @26
    @11
    @29
    cC
    wcel
    #
    @32
    @17
    wceq
    wph
    @11
    @25
    frlmup.t
    adantr
    wph
    @37
    @35
    @44
    @25
    frlmup.a
    @40
    cI
    cC
    @15
    cA
    ffvelrn
    syl2an
    c.x
    @10
    @31
    cC
    cT
    @29
    @17
    frlmup.c
    @12
    frlmup.v
    @31
    eqid
    @18
    lmod0vs
    syl2anc
    3eqtrd
    suppss
    gsumpt
    wph
    @5
    cY
    @0
    cfv
    #
    @6
    c.x
    co
    #
    @10
    cur
    cfv
    #
    @6
    c.x
    co
    #
    @6
    wph
    @33
    @34
    @9
    @43
    @5
    @46
    wceq
    @36
    @38
    frlmup.i
    frlmup.y
    cI
    c.x
    @0
    cA
    cX
    cY
    fnfvof
    syl22anc
    wph
    @45
    @47
    @6
    c.x
    wph
    @45
    cR
    cur
    cfv
    #
    @47
    wph
    cR
    cU
    @49
    cI
    cY
    crg
    cX
    frlmup.u
    @13
    frlmup.i
    frlmup.y
    @49
    eqid
    uvcvv1
    wph
    cR
    @10
    cur
    frlmup.r
    fveq2d
    eqtrd
    oveq1d
    wph
    @11
    @6
    cC
    wcel
    @48
    @6
    wceq
    frlmup.t
    wph
    cI
    cC
    cY
    cA
    frlmup.a
    frlmup.y
    ffvelrnd
    c.x
    @47
    @10
    cC
    cT
    @6
    frlmup.c
    @12
    frlmup.v
    @47
    eqid
    lmodvs1
    syl2anc
    3eqtrd
    3eqtrd
end
