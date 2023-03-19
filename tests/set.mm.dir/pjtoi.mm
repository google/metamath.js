include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "chos.mm"
include "co.mm"
include "chil.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "cva.mm"
include "cch.mm"
include "axpjpj.mm"
include "mpan.mm"
include "pjch1.mm"
include "wf.mm"
include "pjfi.mm"
include "choccli.mm"
include "hosval.mm"
include "mp3an12.mm"
include "3eqtr4rd.mm"
include "rgen.mm"
include "hoaddcli.mm"
include "helch.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem pjtoi
  let cH: class H
  let vx: setvar x
  assume pjidmco.1: |- H e. CH


  assert |- ( ( projh ` H ) +op ( projh ` ( _|_ ` H ) ) ) = ( projh ` ~H )

  proof
    vx
    cv
    #
    cH
    cpjh
    cfv
    #
    cH
    cort
    cfv
    #
    cpjh
    cfv
    #
    chos
    co
    #
    cfv
    #
    @0
    chil
    cpjh
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @4
    @6
    wceq
    @8
    vx
    chil
    @0
    chil
    wcel
    #
    @0
    @0
    @1
    cfv
    @0
    @3
    cfv
    cva
    co
    #
    @7
    @5
    cH
    cch
    wcel
    @9
    @0
    @10
    wceq
    pjidmco.1
    @0
    cH
    axpjpj
    mpan
    @0
    pjch1
    chil
    chil
    @1
    wf
    chil
    chil
    @3
    wf
    @9
    @5
    @10
    wceq
    cH
    pjidmco.1
    pjfi
    #
    @2
    cH
    pjidmco.1
    choccli
    pjfi
    #
    @0
    @1
    @3
    hosval
    mp3an12
    3eqtr4rd
    rgen
    vx
    @4
    @6
    @1
    @3
    @11
    @12
    hoaddcli
    chil
    helch
    pjfi
    hoeqi
    mpbi
end
