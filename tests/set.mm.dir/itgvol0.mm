include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "citg.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "mpt0.mm"
include "iblempty.mm"
include "eqeltri.mm"
include "wb.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "cdif.mm"
include "cr.mm"
include "covol.mm"
include "cfv.mm"
include "difssd.mm"
include "ovolssnul.mm"
include "syl3anc.mm"
include "itgss3.mm"
include "simpld.mm"
include "mpbii.mm"
include "itg0.mm"
include "simprd.mm"
include "syl5reqr.mm"
include "jca.mm"

theorem itgvol0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume itgvol0.1: |- ( ph -> A C_ RR )
  assume itgvol0.2: |- ( ph -> ( vol* ` A ) = 0 )
  assume itgvol0.3: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint A x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 /\ S. A B _d x = 0 ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    cibl
    wcel
    #
    vx
    cA
    cB
    citg
    #
    cc0
    wceq
    wph
    vx
    c0
    cB
    cmpt
    #
    cibl
    wcel
    #
    @0
    @2
    c0
    cibl
    vx
    cB
    mpt0
    iblempty
    eqeltri
    wph
    @3
    @0
    wb
    #
    vx
    c0
    cB
    citg
    #
    @1
    wceq
    #
    wph
    vx
    c0
    cA
    cB
    c0
    cA
    wss
    wph
    cA
    0ss
    a1i
    itgvol0.1
    wph
    cA
    c0
    cdif
    #
    cA
    wss
    cA
    cr
    wss
    cA
    covol
    cfv
    cc0
    wceq
    @7
    covol
    cfv
    cc0
    wceq
    wph
    cA
    c0
    difssd
    itgvol0.1
    itgvol0.2
    @7
    cA
    ovolssnul
    syl3anc
    itgvol0.3
    itgss3
    #
    simpld
    mpbii
    wph
    cc0
    @5
    @1
    vx
    cB
    itg0
    wph
    @4
    @6
    @8
    simprd
    syl5reqr
    jca
end
