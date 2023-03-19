include "cun.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wceq.mm"
include "undif2.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "a1i.mm"
include "csalg.mm"
include "wcel.mm"
include "dmmeasal.mm"
include "saldifcl2.mm"
include "syl3anc.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "meadjun.mm"
include "eqtrd.mm"
include "meaxrcl.mm"
include "difssd.mm"
include "meassle.mm"
include "xleadd2d.mm"
include "eqbrtrd.mm"

theorem meaunle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meaunle.1: |- ( ph -> M e. Meas )
  assume meaunle.2: |- S = dom M
  assume meaunle.3: |- ( ph -> A e. S )
  assume meaunle.4: |- ( ph -> B e. S )


  assert |- ( ph -> ( M ` ( A u. B ) ) <_ ( ( M ` A ) +e ( M ` B ) ) )

  proof
    wph
    cA
    cB
    cun
    #
    cM
    cfv
    #
    cA
    cM
    cfv
    #
    cB
    cA
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @2
    cB
    cM
    cfv
    #
    cxad
    co
    cle
    wph
    @1
    cA
    @3
    cun
    #
    cM
    cfv
    #
    @5
    @1
    @8
    wceq
    wph
    @0
    @7
    cM
    @7
    @0
    cA
    cB
    undif2
    eqcomi
    fveq2i
    a1i
    wph
    cA
    @3
    cS
    cM
    meaunle.1
    meaunle.2
    meaunle.3
    wph
    cS
    csalg
    wcel
    cB
    cS
    wcel
    cA
    cS
    wcel
    @3
    cS
    wcel
    wph
    cS
    cM
    meaunle.1
    meaunle.2
    dmmeasal
    meaunle.4
    meaunle.3
    cS
    cB
    cA
    saldifcl2
    syl3anc
    #
    cA
    @3
    cin
    c0
    wceq
    wph
    cA
    cB
    disjdif
    a1i
    meadjun
    eqtrd
    wph
    @4
    @6
    @2
    wph
    @3
    cS
    cM
    meaunle.1
    meaunle.2
    @9
    meaxrcl
    wph
    cB
    cS
    cM
    meaunle.1
    meaunle.2
    meaunle.4
    meaxrcl
    wph
    cA
    cS
    cM
    meaunle.1
    meaunle.2
    meaunle.3
    meaxrcl
    wph
    @3
    cB
    cS
    cM
    meaunle.1
    meaunle.2
    @9
    meaunle.4
    wph
    cB
    cA
    difssd
    meassle
    xleadd2d
    eqbrtrd
end
