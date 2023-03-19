include "cmin.mm"
include "co.mm"
include "cpi.mm"
include "wceq.mm"
include "cdiv.mm"
include "cneg.mm"
include "crp.mm"
include "wcel.mm"
include "wne.mm"
include "angpieqvdlem2.mm"
include "wa.mm"
include "c1.mm"
include "wn.mm"
include "1rp.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "1re.mm"
include "ax-1ne0.mm"
include "rpneg.mm"
include "mp2an.mm"
include "mpbi.mm"
include "cc.mm"
include "subcld.mm"
include "adantr.mm"
include "subne0d.mm"
include "simpr.mm"
include "oveq1d.mm"
include "diveq1bd.mm"
include "adantlr.mm"
include "negeqd.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpi.mm"
include "necom.mm"
include "syl6ib.mm"
include "sylbird.mm"

theorem angpined
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume angpieqvd.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume angpieqvd.A: |- ( ph -> A e. CC )
  assume angpieqvd.B: |- ( ph -> B e. CC )
  assume angpieqvd.C: |- ( ph -> C e. CC )
  assume angpieqvd.AneB: |- ( ph -> A =/= B )
  assume angpieqvd.BneC: |- ( ph -> B =/= C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( ( ( A - B ) F ( C - B ) ) = _pi -> A =/= C ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    cF
    co
    cpi
    wceq
    @1
    @0
    cdiv
    co
    #
    cneg
    #
    crp
    wcel
    #
    cA
    cC
    wne
    #
    wph
    vx
    vy
    cA
    cB
    cC
    cF
    angpieqvd.angdef
    angpieqvd.A
    angpieqvd.B
    angpieqvd.C
    angpieqvd.AneB
    angpieqvd.BneC
    angpieqvdlem2
    wph
    @4
    cC
    cA
    wne
    #
    @5
    wph
    @4
    @6
    wph
    @4
    wa
    #
    c1
    cneg
    #
    crp
    wcel
    #
    wn
    #
    @6
    c1
    crp
    wcel
    #
    @10
    1rp
    c1
    cr
    wcel
    c1
    cc0
    wne
    @11
    @10
    wb
    1re
    ax-1ne0
    c1
    rpneg
    mp2an
    mpbi
    @7
    @9
    cC
    cA
    @7
    cC
    cA
    wceq
    #
    @9
    @7
    @12
    wa
    #
    @3
    @8
    crp
    @13
    @2
    c1
    wph
    @12
    @2
    c1
    wceq
    @4
    wph
    @12
    wa
    #
    @1
    @0
    wph
    @0
    cc
    wcel
    @12
    wph
    cA
    cB
    angpieqvd.A
    angpieqvd.B
    subcld
    adantr
    wph
    @0
    cc0
    wne
    @12
    wph
    cA
    cB
    angpieqvd.A
    angpieqvd.B
    angpieqvd.AneB
    subne0d
    adantr
    @14
    cC
    cA
    cB
    cmin
    wph
    @12
    simpr
    oveq1d
    diveq1bd
    adantlr
    negeqd
    wph
    @4
    @12
    simplr
    eqeltrrd
    ex
    necon3bd
    mpi
    ex
    cC
    cA
    necom
    syl6ib
    sylbird
end
