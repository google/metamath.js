include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "volico.mm"
include "syl2anc.mm"
include "iftrued.mm"
include "eqtrd.mm"

theorem volicon0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume volicon0.1: |- ( ph -> A e. RR )
  assume volicon0.2: |- ( ph -> B e. RR )
  assume volicon0.3: |- ( ph -> A < B )


  assert |- ( ph -> ( vol ` ( A [,) B ) ) = ( B - A ) )

  proof
    wph
    cA
    cB
    cico
    co
    cvol
    cfv
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    #
    cc0
    cif
    #
    @2
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @3
    wceq
    volicon0.1
    volicon0.2
    cA
    cB
    volico
    syl2anc
    wph
    @1
    @2
    cc0
    volicon0.3
    iftrued
    eqtrd
end
