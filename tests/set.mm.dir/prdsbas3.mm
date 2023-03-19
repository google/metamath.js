include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cbs.mm"
include "cixp.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "prdsbas2.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvixp.mm"
include "syl6eq.mm"
include "wa.mm"
include "fvmpt2.mm"
include "syl6eqr.mm"
include "ralimiaa.mm"
include "ixpeq2.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem prdsbas3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let cF: class F
  let cG: class G
  assume prdsbasmpt2.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsbasmpt2.b: |- B = ( Base ` Y )
  assume prdsbasmpt2.s: |- ( ph -> S e. V )
  assume prdsbasmpt2.i: |- ( ph -> I e. W )
  assume prdsbasmpt2.r: |- ( ph -> A. x e. I R e. X )
  assume prdsbasmpt2.k: |- K = ( Base ` R )

  disjoint I x
  disjoint B y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint ph y
  disjoint S y
  disjoint V y
  disjoint I y
  disjoint R y
  disjoint W y
  disjoint Y y
  assert |- ( ph -> B = X_ x e. I K )

  proof
    wph
    cB
    vx
    cI
    vx
    cv
    #
    vx
    cI
    cR
    cmpt
    #
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    vx
    cI
    cK
    cixp
    #
    wph
    cB
    vy
    cI
    vy
    cv
    #
    @1
    cfv
    #
    cbs
    cfv
    #
    cixp
    @4
    wph
    vy
    cB
    @1
    cS
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
    @1
    cI
    wfn
    prdsbasmpt2.r
    vx
    cI
    cR
    @1
    cX
    @1
    eqid
    #
    fnmpt
    syl
    prdsbas2
    vy
    vx
    cI
    @8
    @3
    vx
    @7
    cbs
    vx
    cbs
    nfcv
    vx
    cI
    cR
    @6
    nffvmpt1
    nffv
    vy
    @3
    nfcv
    @6
    @0
    wceq
    @7
    @2
    cbs
    @6
    @0
    @1
    fveq2
    fveq2d
    cbvixp
    syl6eq
    wph
    @10
    @3
    cK
    wceq
    #
    vx
    cI
    wral
    @4
    @5
    wceq
    prdsbasmpt2.r
    @9
    @12
    vx
    cI
    @0
    cI
    wcel
    @9
    wa
    #
    @3
    cR
    cbs
    cfv
    cK
    @13
    @2
    cR
    cbs
    vx
    cI
    cR
    cX
    @1
    @11
    fvmpt2
    fveq2d
    prdsbasmpt2.k
    syl6eqr
    ralimiaa
    vx
    cI
    @3
    cK
    ixpeq2
    3syl
    eqtrd
end
