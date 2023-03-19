include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cxne.mm"
include "clsi.mm"
include "cneg.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "rexrd.mm"
include "limsupvaluz3.mm"
include "rexnegd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "xnegeqd.mm"
include "eqtrd.mm"

theorem limsupvaluz4
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume limsupvaluz4.k: |- F/ k ph
  assume limsupvaluz4.m: |- ( ph -> M e. ZZ )
  assume limsupvaluz4.z: |- Z = ( ZZ>= ` M )
  assume limsupvaluz4.b: |- ( ( ph /\ k e. Z ) -> B e. RR )

  disjoint M k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( limsup ` ( k e. Z |-> B ) ) = -e ( liminf ` ( k e. Z |-> -u B ) ) )

  proof
    wph
    vk
    cZ
    cB
    cmpt
    clsp
    cfv
    vk
    cZ
    cB
    cxne
    #
    cmpt
    #
    clsi
    cfv
    #
    cxne
    vk
    cZ
    cB
    cneg
    #
    cmpt
    #
    clsi
    cfv
    #
    cxne
    wph
    cB
    vk
    cM
    cZ
    limsupvaluz4.k
    limsupvaluz4.m
    limsupvaluz4.z
    wph
    vk
    cv
    cZ
    wcel
    wa
    #
    cB
    limsupvaluz4.b
    rexrd
    limsupvaluz3
    wph
    @2
    @5
    wph
    @1
    @4
    clsi
    wph
    vk
    cZ
    @0
    @3
    limsupvaluz4.k
    @6
    cB
    limsupvaluz4.b
    rexnegd
    mpteq2da
    fveq2d
    xnegeqd
    eqtrd
end
