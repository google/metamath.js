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
include "cioo.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "ioombl.mm"
include "cnmbf.mm"
include "sylancr.mm"
include "wf.mm"
include "wceq.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "fveq2d.mm"
include "ioovolcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "bddibl.mm"
include "syl3anc.mm"

theorem cnioobibld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  assume cnioobibld.1: |- ( ph -> A e. RR )
  assume cnioobibld.2: |- ( ph -> B e. RR )
  assume cnioobibld.3: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume cnioobibld.4: |- ( ph -> E. x e. RR A. y e. dom F ( abs ` ( F ` y ) ) <_ x )

  disjoint x y
  disjoint F x
  disjoint F y
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
    cB
    cioo
    co
    #
    cvol
    cdm
    wcel
    cF
    @3
    cc
    ccncf
    co
    wcel
    #
    @0
    cA
    cB
    ioombl
    cnioobibld.3
    @3
    cF
    cnmbf
    sylancr
    wph
    @2
    @3
    cvol
    cfv
    #
    cr
    wph
    @1
    @3
    cvol
    wph
    @4
    @3
    cc
    cF
    wf
    @1
    @3
    wceq
    cnioobibld.3
    @3
    cc
    cF
    cncff
    @3
    cc
    cF
    fdm
    3syl
    fveq2d
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @5
    cr
    wcel
    cnioobibld.1
    cnioobibld.2
    cA
    cB
    ioovolcl
    syl2anc
    eqeltrd
    cnioobibld.4
    vx
    vy
    cF
    bddibl
    syl3anc
end
