include "cmpt.mm"
include "clsi.mm"
include "cfv.mm"
include "cxne.mm"
include "clsp.mm"
include "cneg.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "rexrd.mm"
include "liminfvaluz.mm"
include "rexnegd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "xnegeqd.mm"
include "eqtrd.mm"

theorem liminfvaluz2
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume liminfvaluz2.k: |- F/ k ph
  assume liminfvaluz2.m: |- ( ph -> M e. ZZ )
  assume liminfvaluz2.z: |- Z = ( ZZ>= ` M )
  assume liminfvaluz2.b: |- ( ( ph /\ k e. Z ) -> B e. RR )

  disjoint M k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( liminf ` ( k e. Z |-> B ) ) = -e ( limsup ` ( k e. Z |-> -u B ) ) )

  proof
    wph
    vk
    cZ
    cB
    cmpt
    clsi
    cfv
    vk
    cZ
    cB
    cxne
    #
    cmpt
    #
    clsp
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
    clsp
    cfv
    #
    cxne
    wph
    cB
    vk
    cM
    cZ
    liminfvaluz2.k
    liminfvaluz2.m
    liminfvaluz2.z
    wph
    vk
    cv
    cZ
    wcel
    wa
    #
    cB
    liminfvaluz2.b
    rexrd
    liminfvaluz
    wph
    @2
    @5
    wph
    @1
    @4
    clsp
    wph
    vk
    cZ
    @0
    @3
    liminfvaluz2.k
    @6
    cB
    liminfvaluz2.b
    rexnegd
    mpteq2da
    fveq2d
    xnegeqd
    eqtrd
end
