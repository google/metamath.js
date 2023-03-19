include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cmin.mm"
include "cabs.mm"
include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "zred.mm"
include "dnival.mm"
include "syl.mm"
include "cz.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "flzadd.mm"
include "cico.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "rexri.mm"
include "0re.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "halflt1.mm"
include "3pm3.2i.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "pm3.2i.mm"
include "elico1.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "ico01fl0.mm"
include "oveq2d.mm"
include "recnd.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "subidd.mm"
include "fveq2d.mm"
include "abs0.mm"

theorem dnizeq0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cT: class T
  assume dnizeq0.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnizeq0.1: |- ( ph -> A e. ZZ )

  disjoint A x
  assert |- ( ph -> ( T ` A ) = 0 )

  proof
    wph
    cA
    cT
    cfv
    #
    cA
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    cfl
    cfv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cc0
    wph
    cA
    cr
    wcel
    @0
    @4
    wceq
    wph
    cA
    dnizeq0.1
    zred
    #
    vx
    cA
    cT
    dnizeq0.t
    dnival
    syl
    wph
    @4
    cc0
    cabs
    cfv
    #
    cc0
    wph
    @3
    cc0
    cabs
    wph
    @3
    cA
    cA
    cmin
    co
    cc0
    wph
    @2
    cA
    cA
    cmin
    wph
    @2
    cA
    @1
    cfl
    cfv
    #
    caddc
    co
    #
    cA
    wph
    cA
    cz
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    @2
    @8
    wceq
    wph
    @9
    @10
    dnizeq0.1
    @10
    wph
    halfre
    a1i
    jca
    @1
    cA
    flzadd
    syl
    wph
    @8
    cA
    cc0
    caddc
    co
    cA
    wph
    @7
    cc0
    cA
    caddc
    wph
    @1
    cc0
    c1
    cico
    co
    wcel
    #
    @7
    cc0
    wceq
    @11
    wph
    @11
    @1
    cxr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @1
    c1
    clt
    wbr
    #
    w3a
    #
    @12
    @13
    @14
    @1
    halfre
    rexri
    cc0
    @1
    0re
    halfre
    halfgt0
    ltleii
    halflt1
    3pm3.2i
    cc0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    wa
    @11
    @15
    wb
    @16
    @17
    0xr
    c1
    1re
    rexri
    pm3.2i
    cc0
    c1
    @1
    elico1
    ax-mp
    mpbir
    a1i
    @1
    ico01fl0
    syl
    oveq2d
    wph
    cA
    wph
    cA
    @5
    recnd
    #
    addid1d
    eqtrd
    eqtrd
    oveq1d
    wph
    cA
    @18
    subidd
    eqtrd
    fveq2d
    @6
    cc0
    wceq
    wph
    abs0
    a1i
    eqtrd
    eqtrd
end
