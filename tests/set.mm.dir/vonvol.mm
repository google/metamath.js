include "csn.mm"
include "cmap.mm"
include "co.mm"
include "covoln.mm"
include "cfv.mm"
include "covol.mm"
include "cvoln.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "mblss.mm"
include "syl.mm"
include "ovnovol.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "vonvolmbl.mm"
include "mpbird.mm"
include "mblvon.mm"
include "wceq.mm"
include "mblvol.mm"
include "3eqtr4d.mm"

theorem vonvol
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume vonvol.a: |- ( ph -> A e. V )
  assume vonvol.b: |- ( ph -> B e. dom vol )


  assert |- ( ph -> ( ( voln ` { A } ) ` ( B ^m { A } ) ) = ( vol ` B ) )

  proof
    wph
    cB
    cA
    csn
    #
    cmap
    co
    #
    @0
    covoln
    cfv
    cfv
    cB
    covol
    cfv
    #
    @1
    @0
    cvoln
    cfv
    #
    cfv
    cB
    cvol
    cfv
    #
    wph
    cA
    cB
    cV
    vonvol.a
    wph
    cB
    cvol
    cdm
    wcel
    #
    cB
    cr
    wss
    vonvol.b
    cB
    mblss
    syl
    #
    ovnovol
    wph
    @1
    @0
    @0
    cfn
    wcel
    wph
    cA
    snfi
    a1i
    wph
    @1
    @3
    cdm
    wcel
    @5
    vonvol.b
    wph
    cA
    cB
    cV
    vonvol.a
    @6
    vonvolmbl
    mpbird
    mblvon
    wph
    @5
    @4
    @2
    wceq
    vonvol.b
    cB
    mblvol
    syl
    3eqtr4d
end
