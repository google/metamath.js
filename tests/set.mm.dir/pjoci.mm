include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "chod.mm"
include "co.mm"
include "cort.mm"
include "wceq.mm"
include "chos.mm"
include "pjtoi.mm"
include "helch.mm"
include "pjfi.mm"
include "choccli.mm"
include "hodsi.mm"
include "mpbir.mm"

theorem pjoci
  let cH: class H
  let vx: setvar x
  assume pjidmco.1: |- H e. CH


  assert |- ( ( projh ` ~H ) -op ( projh ` H ) ) = ( projh ` ( _|_ ` H ) )

  proof
    chil
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    chod
    co
    cH
    cort
    cfv
    #
    cpjh
    cfv
    #
    wceq
    @1
    @3
    chos
    co
    @0
    wceq
    cH
    pjidmco.1
    pjtoi
    @0
    @1
    @3
    chil
    helch
    pjfi
    cH
    pjidmco.1
    pjfi
    @2
    cH
    pjidmco.1
    choccli
    pjfi
    hodsi
    mpbir
end
