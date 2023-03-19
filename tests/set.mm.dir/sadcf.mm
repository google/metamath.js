include "cn0.mm"
include "c2o.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cseq.mm"
include "wf.mm"
include "cvv.mm"
include "cfv.mm"
include "0nn0.mm"
include "iftrue.mm"
include "eqid.mm"
include "0ex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "cpr.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wa.mm"
include "cop.mm"
include "df-ov.mm"
include "cxp.mm"
include "wral.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prid2.mm"
include "keepel.mm"
include "rgen2w.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "f0cli.mm"
include "nn0uz.mm"
include "0zd.mm"
include "caddc.mm"
include "cuz.mm"
include "fvexd.mm"
include "seqf2.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem sadcf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cK: class K
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> C : NN0 --> 2o )

  proof
    wph
    cn0
    c2o
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    c0
    vc
    cv
    wcel
    wcad
    #
    c1o
    c0
    cif
    #
    cmpt2
    #
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    c0
    @4
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cc0
    cseq
    #
    wf
    cn0
    c2o
    cC
    wf
    wph
    vx
    vy
    c2o
    cvv
    @3
    @8
    cc0
    cn0
    cc0
    @8
    cfv
    #
    c2o
    wcel
    wph
    @10
    c0
    c2o
    cc0
    cn0
    wcel
    @10
    c0
    wceq
    0nn0
    vn
    cc0
    @7
    c0
    cn0
    @8
    @5
    c0
    @6
    iftrue
    @8
    eqid
    0ex
    fvmpt
    ax-mp
    c0
    c0
    c1o
    cpr
    #
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    #
    eqeltri
    a1i
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    c2o
    wcel
    wph
    @13
    c2o
    wcel
    @14
    cvv
    wcel
    wa
    wa
    @15
    @13
    @14
    cop
    #
    @3
    cfv
    c2o
    @13
    @14
    @3
    df-ov
    c2o
    cn0
    cxp
    #
    c2o
    @16
    @3
    @2
    c2o
    wcel
    #
    vm
    cn0
    wral
    vc
    c2o
    wral
    @17
    c2o
    @3
    wf
    @18
    vc
    vm
    c2o
    cn0
    @1
    c1o
    c0
    c2o
    c1o
    @11
    c2o
    c0
    c1o
    c1o
    con0
    1on
    elexi
    prid2
    df2o3
    eleqtrri
    @12
    keepel
    rgen2w
    vc
    vm
    c2o
    cn0
    @2
    c2o
    @3
    @3
    eqid
    fmpt2
    mpbi
    @12
    f0cli
    eqeltri
    a1i
    nn0uz
    wph
    0zd
    wph
    @13
    cc0
    c1
    caddc
    co
    cuz
    cfv
    wcel
    wa
    @13
    @8
    fvexd
    seqf2
    cn0
    c2o
    cC
    @9
    sadval.c
    feq1i
    sylibr
end
