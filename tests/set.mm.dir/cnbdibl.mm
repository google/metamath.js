include "cmbf.mm"
include "wcel.mm"
include "cdm.mm"
include "cvol.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cibl.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "cnmbf.mm"
include "syl2anc.mm"
include "wf.mm"
include "wceq.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "fveq2d.mm"
include "eqeltrd.mm"
include "bddibl.mm"
include "syl3anc.mm"

theorem cnbdibl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume cnbdibl.a: |- ( ph -> A e. dom vol )
  assume cnbdibl.va: |- ( ph -> ( vol ` A ) e. RR )
  assume cnbdibl.f: |- ( ph -> F e. ( A -cn-> CC ) )
  assume cnbdibl.bd: |- ( ph -> E. x e. RR A. y e. dom F ( abs ` ( F ` y ) ) <_ x )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint k x
  assert |- ( ph -> F e. L^1 )

  proof
    wph
    cF
    cmbf
    wcel
    #
    cF
    cdm
    #
    cvol
    cfv
    #
    cr
    wcel
    vy
    cv
    cF
    cfv
    cabs
    cfv
    vx
    cv
    cle
    wbr
    vy
    @1
    wral
    vx
    cr
    wrex
    cF
    cibl
    wcel
    wph
    cA
    cvol
    cdm
    wcel
    cF
    cA
    cc
    ccncf
    co
    wcel
    #
    @0
    cnbdibl.a
    cnbdibl.f
    cA
    cF
    cnmbf
    syl2anc
    wph
    @2
    cA
    cvol
    cfv
    cr
    wph
    @1
    cA
    cvol
    wph
    @3
    cA
    cc
    cF
    wf
    @1
    cA
    wceq
    cnbdibl.f
    cA
    cc
    cF
    cncff
    cA
    cc
    cF
    fdm
    3syl
    fveq2d
    cnbdibl.va
    eqeltrd
    cnbdibl.bd
    vx
    vy
    cF
    bddibl
    syl3anc
end
