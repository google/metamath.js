include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "renegcld.mm"
include "posdifd.mm"
include "recnd.mm"
include "subnegd.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem possumd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume possumd.1: |- ( ph -> A e. RR )
  assume possumd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( 0 < ( A + B ) <-> -u B < A ) )

  proof
    wph
    cB
    cneg
    #
    cA
    clt
    wbr
    cc0
    cA
    @0
    cmin
    co
    #
    clt
    wbr
    cc0
    cA
    cB
    caddc
    co
    #
    clt
    wbr
    wph
    @0
    cA
    wph
    cB
    possumd.2
    renegcld
    possumd.1
    posdifd
    wph
    @1
    @2
    cc0
    clt
    wph
    cA
    cB
    wph
    cA
    possumd.1
    recnd
    wph
    cB
    possumd.2
    recnd
    subnegd
    breq2d
    bitr2d
end
