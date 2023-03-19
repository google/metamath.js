include "cmpt.mm"
include "clsi.mm"
include "cfv.mm"
include "cv.mm"
include "cxne.mm"
include "clsp.mm"
include "nfmpt1.mm"
include "cxr.mm"
include "fmptd2f.mm"
include "liminfvalxr.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "fvmpt2d.mm"
include "xnegeqd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem liminfvalxrmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  assume liminfvalxrmpt.1: |- F/ x ph
  assume liminfvalxrmpt.2: |- ( ph -> A e. V )
  assume liminfvalxrmpt.3: |- ( ( ph /\ x e. A ) -> B e. RR* )

  disjoint A x
  disjoint k x
  assert |- ( ph -> ( liminf ` ( x e. A |-> B ) ) = -e ( limsup ` ( x e. A |-> -e B ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    clsi
    cfv
    vx
    cA
    vx
    cv
    #
    @0
    cfv
    #
    cxne
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    vx
    cA
    cB
    cxne
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    wph
    vx
    cA
    @0
    cV
    vx
    cA
    cB
    nfmpt1
    liminfvalxrmpt.2
    wph
    vx
    cA
    cB
    cxr
    liminfvalxrmpt.1
    liminfvalxrmpt.3
    fmptd2f
    liminfvalxr
    wph
    @5
    @8
    wph
    @4
    @7
    clsp
    wph
    vx
    cA
    @3
    @6
    liminfvalxrmpt.1
    wph
    @1
    cA
    wcel
    wa
    @2
    cB
    wph
    vx
    cA
    cB
    @0
    cxr
    wph
    @0
    eqidd
    liminfvalxrmpt.3
    fvmpt2d
    xnegeqd
    mpteq2da
    fveq2d
    xnegeqd
    eqtrd
end
