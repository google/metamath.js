include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cneg.mm"
include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cpi.mm"
include "wceq.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "subcld.mm"
include "subne0d.mm"
include "divcld.mm"
include "necomd.mm"
include "divne0d.mm"
include "lognegb.mm"
include "syl2anc.mm"
include "angvald.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem angpieqvdlem2
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
  assert |- ( ph -> ( -u ( ( C - B ) / ( A - B ) ) e. RR+ <-> ( ( A - B ) F ( C - B ) ) = _pi ) )

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
    crp
    wcel
    #
    @2
    clog
    cfv
    cim
    cfv
    #
    cpi
    wceq
    #
    @1
    @0
    cF
    co
    #
    cpi
    wceq
    wph
    @2
    cc
    wcel
    @2
    cc0
    wne
    @3
    @5
    wb
    wph
    @0
    @1
    wph
    cC
    cB
    angpieqvd.C
    angpieqvd.B
    subcld
    #
    wph
    cA
    cB
    angpieqvd.A
    angpieqvd.B
    subcld
    #
    wph
    cA
    cB
    angpieqvd.A
    angpieqvd.B
    angpieqvd.AneB
    subne0d
    #
    divcld
    wph
    @0
    @1
    @7
    @8
    wph
    cC
    cB
    angpieqvd.C
    angpieqvd.B
    wph
    cB
    cC
    angpieqvd.BneC
    necomd
    subne0d
    #
    @9
    divne0d
    @2
    lognegb
    syl2anc
    wph
    @6
    @4
    cpi
    wph
    vx
    vy
    cF
    @1
    @0
    angpieqvd.angdef
    @8
    @9
    @7
    @10
    angvald
    eqeq1d
    bitr4d
end
