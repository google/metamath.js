include "cconcat.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "cpfx.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "anbi12d.mm"
include "mpbir2and.mm"
include "eqid.mm"
include "pfxccatin12.mm"
include "sylc.mm"
include "opeq2d.mm"
include "eqtrd.mm"

theorem pfxccatin12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume pfxccatin12d.l: |- ( ph -> ( # ` A ) = L )
  assume pfxccatin12d.w: |- ( ph -> ( A e. Word V /\ B e. Word V ) )
  assume pfxccatin12d.1: |- ( ph -> M e. ( 0 ... L ) )
  assume pfxccatin12d.2: |- ( ph -> N e. ( L ... ( L + ( # ` B ) ) ) )


  assert |- ( ph -> ( ( A ++ B ) substr <. M , N >. ) = ( ( A substr <. M , L >. ) ++ ( B prefix ( N - L ) ) ) )

  proof
    wph
    cA
    cB
    cconcat
    co
    cM
    cN
    cop
    csubstr
    co
    #
    cA
    cM
    cA
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cB
    cN
    @1
    cmin
    co
    #
    cpfx
    co
    #
    cconcat
    co
    #
    cA
    cM
    cL
    cop
    #
    csubstr
    co
    #
    cB
    cN
    cL
    cmin
    co
    #
    cpfx
    co
    #
    cconcat
    co
    wph
    cA
    cV
    cword
    #
    wcel
    cB
    @11
    wcel
    wa
    cM
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cN
    @1
    @1
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @0
    @6
    wceq
    pfxccatin12d.w
    wph
    @18
    cM
    cc0
    cL
    cfz
    co
    #
    wcel
    #
    cN
    cL
    cL
    @14
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    pfxccatin12d.1
    pfxccatin12d.2
    wph
    @13
    @20
    @17
    @23
    wph
    @12
    @19
    cM
    wph
    @1
    cL
    cc0
    cfz
    pfxccatin12d.l
    oveq2d
    eleq2d
    wph
    @16
    @22
    cN
    wph
    @1
    cL
    @15
    @21
    cfz
    pfxccatin12d.l
    wph
    @1
    cL
    @14
    caddc
    pfxccatin12d.l
    oveq1d
    oveq12d
    eleq2d
    anbi12d
    mpbir2and
    cA
    cB
    @1
    cM
    cN
    cV
    @1
    eqid
    pfxccatin12
    sylc
    wph
    @3
    @8
    @5
    @10
    cconcat
    wph
    @2
    @7
    cA
    csubstr
    wph
    @1
    cL
    cM
    pfxccatin12d.l
    opeq2d
    oveq2d
    wph
    @4
    @9
    cB
    cpfx
    wph
    @1
    cL
    cN
    cmin
    pfxccatin12d.l
    oveq2d
    oveq2d
    oveq12d
    eqtrd
end
