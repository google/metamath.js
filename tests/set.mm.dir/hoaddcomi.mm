include "cv.mm"
include "chos.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cva.mm"
include "ffvelrni.mm"
include "ax-hvcom.mm"
include "syl2anc.mm"
include "wf.mm"
include "hosval.mm"
include "mp3an12.mm"
include "3eqtr4d.mm"
include "rgen.mm"
include "hoaddcli.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem hoaddcomi
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S +op T ) = ( T +op S )

  proof
    vx
    cv
    #
    cS
    cT
    chos
    co
    #
    cfv
    #
    @0
    cT
    cS
    chos
    co
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @1
    @3
    wceq
    @5
    vx
    chil
    @0
    chil
    wcel
    #
    @0
    cS
    cfv
    #
    @0
    cT
    cfv
    #
    cva
    co
    #
    @8
    @7
    cva
    co
    #
    @2
    @4
    @6
    @7
    chil
    wcel
    @8
    chil
    wcel
    @9
    @10
    wceq
    chil
    chil
    @0
    cS
    hoeq.1
    ffvelrni
    chil
    chil
    @0
    cT
    hoeq.2
    ffvelrni
    @7
    @8
    ax-hvcom
    syl2anc
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    @6
    @2
    @9
    wceq
    hoeq.1
    hoeq.2
    @0
    cS
    cT
    hosval
    mp3an12
    @12
    @11
    @6
    @4
    @10
    wceq
    hoeq.2
    hoeq.1
    @0
    cT
    cS
    hosval
    mp3an12
    3eqtr4d
    rgen
    vx
    @1
    @3
    cS
    cT
    hoeq.1
    hoeq.2
    hoaddcli
    cT
    cS
    hoeq.2
    hoeq.1
    hoaddcli
    hoeqi
    mpbi
end
