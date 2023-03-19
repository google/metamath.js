include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cneg.mm"
include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "cioo.mm"
include "subcld.mm"
include "subne0d.mm"
include "divcld.mm"
include "negcld.mm"
include "1cnd.mm"
include "necomd.mm"
include "subneintr2d.mm"
include "divne1d.mm"
include "negned.mm"
include "xov1plusxeqvd.mm"
include "divnegd.mm"
include "negsubdi2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "dividd.mm"
include "divsubdird.mm"
include "negsubd.mm"
include "3eqtr4rd.mm"
include "nnncan2d.mm"
include "oveq12d.mm"
include "divcan7d.mm"
include "div2subd.mm"
include "3eqtrrd.mm"
include "eleq1d.mm"
include "bitr4d.mm"

theorem angpieqvdlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume angpieqvdlem.A: |- ( ph -> A e. CC )
  assume angpieqvdlem.B: |- ( ph -> B e. CC )
  assume angpieqvdlem.C: |- ( ph -> C e. CC )
  assume angpieqvdlem.AneB: |- ( ph -> A =/= B )
  assume angpieqvdlem.AneC: |- ( ph -> A =/= C )


  assert |- ( ph -> ( -u ( ( C - B ) / ( A - B ) ) e. RR+ <-> ( ( C - B ) / ( C - A ) ) e. ( 0 (,) 1 ) ) )

  proof
    wph
    cC
    cB
    cmin
    co
    #
    cA
    cB
    cmin
    co
    #
    cdiv
    co
    #
    cneg
    #
    crp
    wcel
    @3
    c1
    @3
    caddc
    co
    #
    cdiv
    co
    #
    cc0
    c1
    cioo
    co
    #
    wcel
    @0
    cC
    cA
    cmin
    co
    cdiv
    co
    #
    @6
    wcel
    wph
    @3
    wph
    @2
    wph
    @0
    @1
    wph
    cC
    cB
    angpieqvdlem.C
    angpieqvdlem.B
    subcld
    #
    wph
    cA
    cB
    angpieqvdlem.A
    angpieqvdlem.B
    subcld
    #
    wph
    cA
    cB
    angpieqvdlem.A
    angpieqvdlem.B
    angpieqvdlem.AneB
    subne0d
    #
    divcld
    #
    negcld
    wph
    @2
    c1
    @11
    wph
    1cnd
    #
    wph
    @0
    @1
    @8
    @9
    @10
    wph
    cC
    cA
    cB
    angpieqvdlem.C
    angpieqvdlem.A
    angpieqvdlem.B
    wph
    cA
    cC
    angpieqvdlem.AneC
    necomd
    subneintr2d
    divne1d
    negned
    xov1plusxeqvd
    wph
    @7
    @5
    @6
    wph
    @5
    cB
    cC
    cmin
    co
    #
    @1
    cdiv
    co
    #
    cA
    cC
    cmin
    co
    #
    @1
    cdiv
    co
    #
    cdiv
    co
    @13
    @15
    cdiv
    co
    @7
    wph
    @3
    @14
    @4
    @16
    cdiv
    wph
    @3
    @0
    cneg
    #
    @1
    cdiv
    co
    @14
    wph
    @0
    @1
    @8
    @9
    @10
    divnegd
    wph
    @17
    @13
    @1
    cdiv
    wph
    cC
    cB
    angpieqvdlem.C
    angpieqvdlem.B
    negsubdi2d
    oveq1d
    eqtrd
    wph
    @4
    @1
    @0
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @16
    wph
    @1
    @1
    cdiv
    co
    #
    @2
    cmin
    co
    c1
    @2
    cmin
    co
    @19
    @4
    wph
    @20
    c1
    @2
    cmin
    wph
    @1
    @9
    @10
    dividd
    oveq1d
    wph
    @1
    @0
    @1
    @9
    @8
    @9
    @10
    divsubdird
    wph
    c1
    @2
    @12
    @11
    negsubd
    3eqtr4rd
    wph
    @18
    @15
    @1
    cdiv
    wph
    cA
    cC
    cB
    angpieqvdlem.A
    angpieqvdlem.C
    angpieqvdlem.B
    nnncan2d
    oveq1d
    eqtrd
    oveq12d
    wph
    @13
    @15
    @1
    wph
    cB
    cC
    angpieqvdlem.B
    angpieqvdlem.C
    subcld
    wph
    cA
    cC
    angpieqvdlem.A
    angpieqvdlem.C
    subcld
    @9
    wph
    cA
    cC
    angpieqvdlem.A
    angpieqvdlem.C
    angpieqvdlem.AneC
    subne0d
    @10
    divcan7d
    wph
    cB
    cC
    cA
    cC
    angpieqvdlem.B
    angpieqvdlem.C
    angpieqvdlem.A
    angpieqvdlem.C
    angpieqvdlem.AneC
    div2subd
    3eqtrrd
    eleq1d
    bitr4d
end
