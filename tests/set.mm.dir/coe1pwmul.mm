include "cur.mm"
include "cfv.mm"
include "co.mm"
include "cvsca.mm"
include "cco1.mm"
include "cn0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cmulr.mm"
include "cif.mm"
include "cmpt.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "ringidcl.mm"
include "syl.mm"
include "coe1tmmul.mm"
include "csca.mm"
include "wceq.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "3syl.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "wa.mm"
include "ad2antrr.mm"
include "wf.mm"
include "coe1f.mm"
include "simplr.mm"
include "simpr.mm"
include "nn0sub2.mm"
include "ffvelrnd.mm"
include "ringlidm.mm"
include "ifeq1da.mm"
include "mpteq2dva.mm"
include "3eqtr3d.mm"

theorem coe1pwmul
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cY: class Y
  assume coe1pwmul.z: |- .0. = ( 0g ` R )
  assume coe1pwmul.p: |- P = ( Poly1 ` R )
  assume coe1pwmul.x: |- X = ( var1 ` R )
  assume coe1pwmul.n: |- N = ( mulGrp ` P )
  assume coe1pwmul.e: |- .^ = ( .g ` N )
  assume coe1pwmul.b: |- B = ( Base ` P )
  assume coe1pwmul.t: |- .x. = ( .r ` P )
  assume coe1pwmul.r: |- ( ph -> R e. Ring )
  assume coe1pwmul.a: |- ( ph -> A e. B )
  assume coe1pwmul.d: |- ( ph -> D e. NN0 )

  disjoint A x
  disjoint D x
  disjoint N x
  disjoint P x
  disjoint R x
  disjoint X x
  disjoint .^ x
  disjoint .0. x
  disjoint ph x
  disjoint .x. x
  disjoint Y x
  assert |- ( ph -> ( coe1 ` ( ( D .^ X ) .x. A ) ) = ( x e. NN0 |-> if ( D <_ x , ( ( coe1 ` A ) ` ( x - D ) ) , .0. ) ) )

  proof
    wph
    cR
    cur
    cfv
    #
    cD
    cX
    c.ex
    co
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cA
    c.x
    co
    #
    cco1
    cfv
    vx
    cn0
    cD
    vx
    cv
    #
    cle
    wbr
    #
    @0
    @5
    cD
    cmin
    co
    #
    cA
    cco1
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    cif
    #
    cmpt
    @1
    cA
    c.x
    co
    #
    cco1
    cfv
    vx
    cn0
    @6
    @9
    c.0
    cif
    #
    cmpt
    wph
    vx
    cA
    cB
    @0
    cD
    cP
    cR
    c.x
    @2
    @10
    c.ex
    cR
    cbs
    cfv
    #
    cN
    cX
    c.0
    coe1pwmul.z
    @15
    eqid
    #
    coe1pwmul.p
    coe1pwmul.x
    @2
    eqid
    #
    coe1pwmul.n
    coe1pwmul.e
    coe1pwmul.b
    coe1pwmul.t
    @10
    eqid
    #
    coe1pwmul.a
    coe1pwmul.r
    wph
    cR
    crg
    wcel
    #
    @0
    @15
    wcel
    coe1pwmul.r
    @15
    cR
    @0
    @16
    @0
    eqid
    #
    ringidcl
    syl
    coe1pwmul.d
    coe1tmmul
    wph
    @4
    @13
    cco1
    wph
    @3
    @1
    cA
    c.x
    wph
    @3
    cP
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    @2
    co
    #
    @1
    wph
    @0
    @22
    @1
    @2
    wph
    cR
    @21
    cur
    wph
    @19
    cR
    @21
    wceq
    coe1pwmul.r
    cP
    cR
    crg
    coe1pwmul.p
    ply1sca
    syl
    fveq2d
    oveq1d
    wph
    cP
    clmod
    wcel
    #
    @1
    cB
    wcel
    #
    @23
    @1
    wceq
    wph
    @19
    @24
    coe1pwmul.r
    cP
    cR
    coe1pwmul.p
    ply1lmod
    syl
    wph
    cN
    cmnd
    wcel
    #
    cD
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    @25
    wph
    @19
    cP
    crg
    wcel
    @26
    coe1pwmul.r
    cP
    cR
    coe1pwmul.p
    ply1ring
    cP
    cN
    coe1pwmul.n
    ringmgp
    3syl
    coe1pwmul.d
    wph
    @19
    @28
    coe1pwmul.r
    cB
    cP
    cR
    cX
    coe1pwmul.x
    coe1pwmul.p
    coe1pwmul.b
    vr1cl
    syl
    cB
    c.ex
    cN
    cD
    cX
    cB
    cP
    cN
    coe1pwmul.n
    coe1pwmul.b
    mgpbas
    coe1pwmul.e
    mulgnn0cl
    syl3anc
    @2
    @22
    @21
    cB
    cP
    @1
    coe1pwmul.b
    @21
    eqid
    @17
    @22
    eqid
    lmodvs1
    syl2anc
    eqtrd
    oveq1d
    fveq2d
    wph
    vx
    cn0
    @12
    @14
    wph
    @5
    cn0
    wcel
    #
    wa
    #
    @6
    @11
    @9
    c.0
    @30
    @6
    wa
    #
    @19
    @9
    @15
    wcel
    @11
    @9
    wceq
    wph
    @19
    @29
    @6
    coe1pwmul.r
    ad2antrr
    @31
    cn0
    @15
    @7
    @8
    wph
    cn0
    @15
    @8
    wf
    #
    @29
    @6
    wph
    cA
    cB
    wcel
    @32
    coe1pwmul.a
    @8
    cB
    cP
    cR
    cA
    @15
    @8
    eqid
    coe1pwmul.b
    coe1pwmul.p
    @16
    coe1f
    syl
    ad2antrr
    @31
    @27
    @29
    @6
    @7
    cn0
    wcel
    wph
    @27
    @29
    @6
    coe1pwmul.d
    ad2antrr
    wph
    @29
    @6
    simplr
    @30
    @6
    simpr
    cD
    @5
    nn0sub2
    syl3anc
    ffvelrnd
    @15
    cR
    @10
    @0
    @9
    @16
    @18
    @20
    ringlidm
    syl2anc
    ifeq1da
    mpteq2dva
    3eqtr3d
end
