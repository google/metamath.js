include "cdpj.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cdprd.mm"
include "cmpt.mm"
include "cgrp.mm"
include "cdm.mm"
include "cima.mm"
include "cpj1.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-dpj.mm"
include "a1i.mm"
include "wa.mm"
include "simprr.mm"
include "dmeqd.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "difeq1d.mm"
include "reseq12d.mm"
include "oveq12d.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "simpr.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "wbr.mm"
include "wcel.mm"
include "dprdgrp.mm"
include "syl.mm"
include "wrel.mm"
include "wb.mm"
include "reldmdprd.mm"
include "elrelimasn.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "dprddomcld.mm"
include "mptexg.mm"
include "ovmpt2dx.mm"
include "syl5eq.mm"

theorem dpjfval
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vi: setvar i
  let cG: class G
  let cI: class I
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let cC: class C
  let cW: class W
  let cX: class X
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjfval.q: |- Q = ( proj1 ` G )

  disjoint G i
  disjoint i ph
  disjoint I i
  disjoint S i
  disjoint h k
  disjoint h x
  disjoint .0. h
  disjoint k x
  disjoint .0. k
  disjoint .0. x
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint f s
  disjoint f x
  disjoint G f
  disjoint g h
  disjoint g i
  disjoint g k
  disjoint g s
  disjoint g x
  disjoint G g
  disjoint h i
  disjoint h s
  disjoint G h
  disjoint i k
  disjoint i s
  disjoint i x
  disjoint k s
  disjoint G k
  disjoint s x
  disjoint G s
  disjoint G x
  disjoint P f
  disjoint P h
  disjoint P x
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph s
  disjoint ph x
  disjoint C h
  disjoint I f
  disjoint I g
  disjoint I h
  disjoint I k
  disjoint I s
  disjoint I x
  disjoint Q g
  disjoint Q s
  disjoint Q x
  disjoint W f
  disjoint W k
  disjoint W x
  disjoint X h
  disjoint X x
  disjoint A f
  disjoint A h
  disjoint A k
  disjoint A x
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S k
  disjoint S s
  disjoint S x
  disjoint Y x
  assert |- ( ph -> P = ( i e. I |-> ( ( S ` i ) Q ( G DProd ( S |` ( I \ { i } ) ) ) ) ) )

  proof
    wph
    cP
    cG
    cS
    cdpj
    co
    vi
    cI
    vi
    cv
    #
    cS
    cfv
    #
    cG
    cS
    cI
    @0
    csn
    #
    cdif
    #
    cres
    #
    cdprd
    co
    #
    cQ
    co
    #
    cmpt
    #
    dpjfval.p
    wph
    vg
    vs
    cG
    cS
    cgrp
    cdprd
    cdm
    #
    vg
    cv
    #
    csn
    #
    cima
    #
    vi
    vs
    cv
    #
    cdm
    #
    @0
    @12
    cfv
    #
    @9
    @12
    @13
    @2
    cdif
    #
    cres
    #
    cdprd
    co
    #
    @9
    cpj1
    cfv
    #
    co
    #
    cmpt
    #
    @7
    cdpj
    @8
    cG
    csn
    #
    cima
    #
    cvv
    cdpj
    vg
    vs
    cgrp
    @11
    @20
    cmpt2
    wceq
    wph
    vg
    vi
    vs
    df-dpj
    a1i
    wph
    @9
    cG
    wceq
    #
    @12
    cS
    wceq
    #
    wa
    #
    wa
    #
    vi
    @13
    @19
    cI
    @6
    @26
    @13
    cS
    cdm
    #
    cI
    @26
    @12
    cS
    wph
    @23
    @24
    simprr
    #
    dmeqd
    wph
    @27
    cI
    wceq
    @25
    dpjfval.2
    adantr
    eqtrd
    #
    @26
    @14
    @1
    @17
    @5
    @18
    cQ
    @26
    @18
    cG
    cpj1
    cfv
    cQ
    @26
    @9
    cG
    cpj1
    wph
    @23
    @24
    simprl
    #
    fveq2d
    dpjfval.q
    syl6eqr
    @26
    @0
    @12
    cS
    @28
    fveq1d
    @26
    @9
    cG
    @16
    @4
    cdprd
    @30
    @26
    @12
    cS
    @15
    @3
    @28
    @26
    @13
    cI
    @2
    @29
    difeq1d
    reseq12d
    oveq12d
    oveq123d
    mpteq12dv
    wph
    @23
    wa
    #
    @10
    @21
    @8
    @31
    @9
    cG
    wph
    @23
    simpr
    sneqd
    imaeq2d
    wph
    cG
    cS
    @8
    wbr
    #
    cG
    cgrp
    wcel
    dpjfval.1
    cS
    cG
    dprdgrp
    syl
    wph
    @32
    cS
    @22
    wcel
    #
    dpjfval.1
    @8
    wrel
    @33
    @32
    wb
    reldmdprd
    cG
    cS
    @8
    elrelimasn
    ax-mp
    sylibr
    wph
    cI
    cvv
    wcel
    @7
    cvv
    wcel
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprddomcld
    vi
    cI
    @6
    cvv
    mptexg
    syl
    ovmpt2dx
    syl5eq
end
