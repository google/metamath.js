include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cds.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "prdsdsval.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfov.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq123d.mm"
include "cbvmpt.mm"
include "eqidd.mm"
include "wa.mm"
include "fvmpt2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "ralimiaa.mm"
include "mpteq12.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "uneq1d.mm"
include "supeq1d.mm"
include "eqtrd.mm"

theorem prdsdsval2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume prdsbasmpt2.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsbasmpt2.b: |- B = ( Base ` Y )
  assume prdsbasmpt2.s: |- ( ph -> S e. V )
  assume prdsbasmpt2.i: |- ( ph -> I e. W )
  assume prdsbasmpt2.r: |- ( ph -> A. x e. I R e. X )
  assume prdsdsval2.f: |- ( ph -> F e. B )
  assume prdsdsval2.g: |- ( ph -> G e. B )
  assume prdsdsval2.e: |- E = ( dist ` R )
  assume prdsdsval2.d: |- D = ( dist ` Y )

  disjoint F x
  disjoint G x
  disjoint I x
  disjoint B y
  disjoint x y
  disjoint F y
  disjoint G y
  disjoint ph y
  disjoint S y
  disjoint V y
  disjoint I y
  disjoint R y
  disjoint W y
  disjoint Y y
  assert |- ( ph -> ( F D G ) = sup ( ( ran ( x e. I |-> ( ( F ` x ) E ( G ` x ) ) ) u. { 0 } ) , RR* , < ) )

  proof
    wph
    cF
    cG
    cD
    co
    vy
    cI
    vy
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    @0
    vx
    cI
    cR
    cmpt
    #
    cfv
    #
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @11
    cG
    cfv
    #
    cE
    co
    #
    cmpt
    #
    crn
    #
    @9
    cun
    #
    cxr
    clt
    csup
    wph
    vy
    cB
    cD
    @3
    cS
    cF
    cG
    cI
    cV
    cW
    cY
    prdsbasmpt2.y
    prdsbasmpt2.b
    prdsbasmpt2.s
    prdsbasmpt2.i
    wph
    cR
    cX
    wcel
    #
    vx
    cI
    wral
    #
    @3
    cI
    wfn
    prdsbasmpt2.r
    vx
    cI
    cR
    @3
    cX
    @3
    eqid
    #
    fnmpt
    syl
    prdsdsval2.f
    prdsdsval2.g
    prdsdsval2.d
    prdsdsval
    wph
    cxr
    @10
    @17
    clt
    wph
    @8
    @16
    @9
    wph
    @7
    @15
    wph
    @7
    vx
    cI
    @12
    @13
    @11
    @3
    cfv
    #
    cds
    cfv
    #
    co
    #
    cmpt
    #
    @15
    vy
    vx
    cI
    @6
    @23
    vx
    @1
    @2
    @5
    vx
    @1
    nfcv
    vx
    @4
    cds
    vx
    cds
    nfcv
    vx
    cI
    cR
    @0
    nffvmpt1
    nffv
    vx
    @2
    nfcv
    nfov
    vy
    @23
    nfcv
    @0
    @11
    wceq
    #
    @1
    @12
    @2
    @13
    @5
    @22
    @25
    @4
    @21
    cds
    @0
    @11
    @3
    fveq2
    fveq2d
    @0
    @11
    cF
    fveq2
    @0
    @11
    cG
    fveq2
    oveq123d
    cbvmpt
    wph
    cI
    cI
    wceq
    @23
    @14
    wceq
    #
    vx
    cI
    wral
    #
    @24
    @15
    wceq
    wph
    cI
    eqidd
    wph
    @19
    @27
    prdsbasmpt2.r
    @18
    @26
    vx
    cI
    @11
    cI
    wcel
    @18
    wa
    #
    @22
    cE
    @12
    @13
    @28
    @22
    cR
    cds
    cfv
    cE
    @28
    @21
    cR
    cds
    vx
    cI
    cR
    cX
    @3
    @20
    fvmpt2
    fveq2d
    prdsdsval2.e
    syl6eqr
    oveqd
    ralimiaa
    syl
    vx
    cI
    @23
    cI
    @14
    mpteq12
    syl2anc
    syl5eq
    rneqd
    uneq1d
    supeq1d
    eqtrd
end
