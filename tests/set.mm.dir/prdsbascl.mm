include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "prdsbasfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "eqeltrrd.mm"
include "prdsbasmpt2.mm"
include "mpbid.mm"

theorem prdsbascl
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let cG: class G
  assume prdsbasmpt2.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsbasmpt2.b: |- B = ( Base ` Y )
  assume prdsbasmpt2.s: |- ( ph -> S e. V )
  assume prdsbasmpt2.i: |- ( ph -> I e. W )
  assume prdsbasmpt2.r: |- ( ph -> A. x e. I R e. X )
  assume prdsbasmpt2.k: |- K = ( Base ` R )
  assume prdsbascl.f: |- ( ph -> F e. B )

  disjoint F x
  disjoint I x
  disjoint B y
  disjoint x y
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
  assert |- ( ph -> A. x e. I ( F ` x ) e. K )

  proof
    wph
    vx
    cI
    vx
    cv
    cF
    cfv
    #
    cmpt
    #
    cB
    wcel
    @0
    cK
    wcel
    vx
    cI
    wral
    wph
    cF
    @1
    cB
    wph
    cF
    cI
    wfn
    cF
    @1
    wceq
    wph
    cB
    vx
    cI
    cR
    cmpt
    #
    cS
    cF
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
    vx
    cI
    wral
    @2
    cI
    wfn
    prdsbasmpt2.r
    vx
    cI
    cR
    @2
    cX
    @2
    eqid
    fnmpt
    syl
    prdsbascl.f
    prdsbasfn
    vx
    cI
    cF
    dffn5
    sylib
    prdsbascl.f
    eqeltrrd
    wph
    vx
    cB
    cR
    cS
    @0
    cI
    cK
    cV
    cW
    cX
    cY
    prdsbasmpt2.y
    prdsbasmpt2.b
    prdsbasmpt2.s
    prdsbasmpt2.i
    prdsbasmpt2.r
    prdsbasmpt2.k
    prdsbasmpt2
    mpbid
end
