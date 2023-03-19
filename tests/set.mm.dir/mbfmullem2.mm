include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmbf.mm"
include "cvol.mm"
include "cdm.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "wceq.mm"
include "fdm.mm"
include "wcel.mm"
include "mbfdm.mm"
include "eqeltrrd.mm"
include "inidm.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "nnex.mm"
include "mptex.mm"
include "a1i.mm"
include "cc.mm"
include "citg1.mm"
include "ffvelrnda.mm"
include "i1ff.mm"
include "adantlr.mm"
include "wss.mm"
include "mblss.mm"
include "sselda.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "fvex.mm"
include "eqtr4d.mm"
include "climmul.mm"
include "cres.mm"
include "resmptd.mm"
include "reex.mm"
include "i1fmul.mm"
include "i1fmbf.mm"
include "mbfres.mm"
include "syl2anc.mm"
include "mbflim.mm"
include "eqeltrd.mm"

theorem mbfmullem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  assume mbfmul.1: |- ( ph -> F e. MblFn )
  assume mbfmul.2: |- ( ph -> G e. MblFn )
  assume mbfmul.3: |- ( ph -> F : A --> RR )
  assume mbfmul.4: |- ( ph -> G : A --> RR )
  assume mbfmul.5: |- ( ph -> P : NN --> dom S.1 )
  assume mbfmul.6: |- ( ( ph /\ x e. A ) -> ( n e. NN |-> ( ( P ` n ) ` x ) ) ~~> ( F ` x ) )
  assume mbfmul.7: |- ( ph -> Q : NN --> dom S.1 )
  assume mbfmul.8: |- ( ( ph /\ x e. A ) -> ( n e. NN |-> ( ( Q ` n ) ` x ) ) ~~> ( G ` x ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint P n
  disjoint P x
  disjoint n ph
  disjoint ph x
  disjoint Q n
  disjoint Q x
  disjoint F n
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint P k
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint Q k
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G m
  disjoint G y
  assert |- ( ph -> ( F oF x. G ) e. MblFn )

  proof
    wph
    cF
    cG
    cmul
    cof
    #
    co
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    cmul
    co
    #
    cmpt
    cmbf
    wph
    vx
    cA
    cA
    @2
    @3
    cmul
    cA
    cF
    cG
    cvol
    cdm
    #
    @5
    wph
    cA
    cr
    cF
    wf
    #
    cF
    cA
    wfn
    mbfmul.3
    cA
    cr
    cF
    ffn
    syl
    wph
    cA
    cr
    cG
    wf
    cG
    cA
    wfn
    mbfmul.4
    cA
    cr
    cG
    ffn
    syl
    wph
    cF
    cdm
    #
    cA
    @5
    wph
    @6
    @7
    cA
    wceq
    mbfmul.3
    cA
    cr
    cF
    fdm
    syl
    wph
    cF
    cmbf
    wcel
    @7
    @5
    wcel
    mbfmul.1
    cF
    mbfdm
    syl
    eqeltrrd
    #
    @8
    cA
    inidm
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @2
    eqidd
    @10
    @3
    eqidd
    offval
    wph
    vx
    cA
    @1
    vn
    cv
    #
    cP
    cfv
    #
    cfv
    #
    @1
    @11
    cQ
    cfv
    #
    cfv
    #
    cmul
    co
    #
    @4
    vn
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    @10
    @2
    @3
    vk
    vn
    cn
    @13
    cmpt
    #
    vn
    cn
    @15
    cmpt
    #
    vn
    cn
    @16
    cmpt
    #
    c1
    cvv
    cn
    nnuz
    @10
    1zzd
    mbfmul.6
    @19
    cvv
    wcel
    @10
    vn
    cn
    @16
    nnex
    mptex
    a1i
    mbfmul.8
    @10
    cn
    cc
    vk
    cv
    #
    @17
    @10
    vn
    cn
    @13
    cc
    @17
    @10
    @11
    cn
    wcel
    #
    wa
    #
    @13
    @22
    cr
    cr
    @1
    @12
    wph
    @21
    cr
    cr
    @12
    wf
    #
    @9
    wph
    @21
    wa
    #
    @12
    citg1
    cdm
    #
    wcel
    @23
    wph
    cn
    @25
    @11
    cP
    mbfmul.5
    ffvelrnda
    #
    @12
    i1ff
    syl
    #
    adantlr
    @10
    @1
    cr
    wcel
    #
    @21
    wph
    cA
    cr
    @1
    wph
    cA
    @5
    wcel
    #
    cA
    cr
    wss
    #
    @8
    cA
    mblss
    syl
    #
    sselda
    adantr
    #
    ffvelrnd
    recnd
    @17
    eqid
    #
    fmptd
    ffvelrnda
    @10
    cn
    cc
    @20
    @18
    @10
    vn
    cn
    @15
    cc
    @18
    @22
    @15
    @22
    cr
    cr
    @1
    @14
    wph
    @21
    cr
    cr
    @14
    wf
    #
    @9
    @24
    @14
    @25
    wcel
    @34
    wph
    cn
    @25
    @11
    cQ
    mbfmul.7
    ffvelrnda
    #
    @14
    i1ff
    syl
    #
    adantlr
    @32
    ffvelrnd
    recnd
    @18
    eqid
    #
    fmptd
    ffvelrnda
    @10
    @20
    cn
    wcel
    #
    wa
    @20
    @19
    cfv
    #
    @1
    @20
    cP
    cfv
    #
    cfv
    #
    @1
    @20
    cQ
    cfv
    #
    cfv
    #
    cmul
    co
    #
    @20
    @17
    cfv
    #
    @20
    @18
    cfv
    #
    cmul
    co
    #
    @38
    @39
    @44
    wceq
    @10
    vn
    @20
    @16
    @44
    cn
    @19
    @11
    @20
    wceq
    #
    @13
    @41
    @15
    @43
    cmul
    @48
    @1
    @12
    @40
    @11
    @20
    cP
    fveq2
    fveq1d
    #
    @48
    @1
    @14
    @42
    @11
    @20
    cQ
    fveq2
    fveq1d
    #
    oveq12d
    @19
    eqid
    @41
    @43
    cmul
    ovex
    fvmpt
    adantl
    @38
    @47
    @44
    wceq
    @10
    @38
    @45
    @41
    @46
    @43
    cmul
    vn
    @20
    @13
    @41
    cn
    @17
    @49
    @33
    @1
    @40
    fvex
    fvmpt
    vn
    @20
    @15
    @43
    cn
    @18
    @50
    @37
    @1
    @42
    fvex
    fvmpt
    oveq12d
    adantl
    eqtr4d
    climmul
    @24
    vx
    cr
    @16
    cmpt
    #
    cA
    cres
    #
    vx
    cA
    @16
    cmpt
    cmbf
    @24
    vx
    cr
    cA
    @16
    wph
    @30
    @21
    @31
    adantr
    resmptd
    @24
    @51
    cmbf
    wcel
    @29
    @52
    cmbf
    wcel
    @24
    @12
    @14
    @0
    co
    #
    @51
    cmbf
    @24
    vx
    cr
    cr
    @13
    @15
    cmul
    cr
    @12
    @14
    cvv
    cvv
    @24
    @23
    @12
    cr
    wfn
    @27
    cr
    cr
    @12
    ffn
    syl
    @24
    @34
    @14
    cr
    wfn
    @36
    cr
    cr
    @14
    ffn
    syl
    cr
    cvv
    wcel
    @24
    reex
    a1i
    #
    @54
    cr
    inidm
    @24
    @28
    wa
    #
    @13
    eqidd
    @55
    @15
    eqidd
    offval
    @24
    @53
    @25
    wcel
    @53
    cmbf
    wcel
    @24
    @12
    @14
    @26
    @35
    i1fmul
    @53
    i1fmbf
    syl
    eqeltrrd
    wph
    @29
    @21
    @8
    adantr
    cA
    @51
    mbfres
    syl2anc
    eqeltrrd
    @16
    cvv
    wcel
    wph
    @21
    @9
    wa
    wa
    @13
    @15
    cmul
    ovex
    a1i
    mbflim
    eqeltrd
end
