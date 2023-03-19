include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfv.mm"
include "cfl.mm"
include "cmin.mm"
include "cabs.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "zred.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "dnival.mm"
include "syl.mm"
include "cz.mm"
include "recnd.mm"
include "addassd.mm"
include "1cnd.mm"
include "2halvesd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "peano2zd.mm"
include "eqeltrd.mm"
include "flid.mm"
include "oveq1d.mm"
include "addcld.mm"
include "pncan2d.mm"
include "fveq2d.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "halfgt0.mm"
include "0re.mm"
include "ltlei.mm"
include "ax-mp.mm"
include "absidd.mm"
include "3eqtrd.mm"

theorem dnizphlfeqhlf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cT: class T
  assume dnizphlfeqhlf.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnizphlfeqhlf.1: |- ( ph -> A e. ZZ )

  disjoint A x
  assert |- ( ph -> ( T ` ( A + ( 1 / 2 ) ) ) = ( 1 / 2 ) )

  proof
    wph
    cA
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cT
    cfv
    #
    @1
    @0
    caddc
    co
    #
    cfl
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    cabs
    cfv
    @0
    wph
    @1
    cr
    wcel
    @2
    @6
    wceq
    wph
    cA
    @0
    wph
    cA
    dnizphlfeqhlf.1
    zred
    #
    @0
    cr
    wcel
    wph
    halfre
    a1i
    #
    readdcld
    vx
    @1
    cT
    dnizphlfeqhlf.t
    dnival
    syl
    wph
    @5
    @0
    cabs
    wph
    @5
    @3
    @1
    cmin
    co
    @0
    wph
    @4
    @3
    @1
    cmin
    wph
    @3
    cz
    wcel
    @4
    @3
    wceq
    wph
    @3
    cA
    c1
    caddc
    co
    #
    cz
    wph
    @3
    cA
    @0
    @0
    caddc
    co
    #
    caddc
    co
    @9
    wph
    cA
    @0
    @0
    wph
    cA
    @7
    recnd
    #
    wph
    @0
    @8
    recnd
    #
    @12
    addassd
    wph
    @10
    c1
    cA
    caddc
    wph
    c1
    wph
    1cnd
    2halvesd
    oveq2d
    eqtrd
    wph
    cA
    dnizphlfeqhlf.1
    peano2zd
    eqeltrd
    @3
    flid
    syl
    oveq1d
    wph
    @1
    @0
    wph
    cA
    @0
    @11
    @12
    addcld
    @12
    pncan2d
    eqtrd
    fveq2d
    wph
    @0
    @8
    cc0
    @0
    cle
    wbr
    #
    wph
    cc0
    @0
    clt
    wbr
    @13
    halfgt0
    cc0
    @0
    0re
    halfre
    ltlei
    ax-mp
    a1i
    absidd
    3eqtrd
end
