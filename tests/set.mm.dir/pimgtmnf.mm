include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "eqidd.mm"
include "fvmpt2d.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "rabbida.mm"
include "nfmpt1.mm"
include "eqid.mm"
include "fmptdf.mm"
include "pimgtmnf2.mm"
include "eqtrd.mm"

theorem pimgtmnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume pimgtmnf.1: |- F/ x ph
  assume pimgtmnf.2: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint k x
  assert |- ( ph -> { x e. A | -oo < B } = A )

  proof
    wph
    cmnf
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    cmnf
    vx
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    crab
    cA
    wph
    @0
    @4
    vx
    cA
    pimgtmnf.1
    wph
    @1
    cA
    wcel
    wa
    #
    cB
    @3
    cmnf
    clt
    @5
    @3
    cB
    wph
    vx
    cA
    cB
    @2
    cr
    wph
    @2
    eqidd
    pimgtmnf.2
    fvmpt2d
    eqcomd
    breq2d
    rabbida
    wph
    vx
    cA
    @2
    vx
    cA
    cB
    nfmpt1
    wph
    vx
    cA
    cB
    cr
    @2
    pimgtmnf.1
    pimgtmnf.2
    @2
    eqid
    fmptdf
    pimgtmnf2
    eqtrd
end
