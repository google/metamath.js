include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "wceq.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "wcel.mm"
include "wral.mm"
include "wi.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccv.mm"
include "syl.mm"
include "imp.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem 2fvcoidd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let vx: setvar x
  assume 2fvcoidd.f: |- ( ph -> F : A --> B )
  assume 2fvcoidd.g: |- ( ph -> G : B --> A )
  assume 2fvcoidd.i: |- ( ph -> A. a e. A ( G ` ( F ` a ) ) = a )

  disjoint A a
  disjoint F a
  disjoint G a
  disjoint A x
  disjoint a x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint ph x
  assert |- ( ph -> ( G o. F ) = ( _I |` A ) )

  proof
    wph
    cG
    cF
    ccom
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cG
    cfv
    #
    cmpt
    #
    cid
    cA
    cres
    #
    wph
    cB
    cA
    cG
    wf
    cA
    cB
    cF
    wf
    @0
    @4
    wceq
    2fvcoidd.g
    2fvcoidd.f
    vx
    cG
    cF
    cA
    cB
    cA
    fcompt
    syl2anc
    wph
    @4
    vx
    cA
    @1
    cmpt
    @5
    wph
    vx
    cA
    @3
    @1
    wph
    @1
    cA
    wcel
    #
    @3
    @1
    wceq
    #
    wph
    va
    cv
    #
    cF
    cfv
    #
    cG
    cfv
    #
    @8
    wceq
    #
    va
    cA
    wral
    @6
    @7
    wi
    2fvcoidd.i
    @11
    @7
    va
    @1
    cA
    va
    vx
    weq
    #
    @10
    @3
    @8
    @1
    @12
    @9
    @2
    cG
    @8
    @1
    cF
    fveq2
    fveq2d
    @12
    id
    eqeq12d
    rspccv
    syl
    imp
    mpteq2dva
    vx
    cA
    mptresid
    syl6eq
    eqtrd
end
