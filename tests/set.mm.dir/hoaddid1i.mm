include "cv.mm"
include "ch0o.mm"
include "chos.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cva.mm"
include "c0v.mm"
include "wf.mm"
include "ho0f.mm"
include "hosval.mm"
include "mp3an12.mm"
include "ho0val.mm"
include "oveq2d.mm"
include "ffvelrni.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "3eqtrd.mm"
include "rgen.mm"
include "hoaddcli.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem hoaddid1i
  let cT: class T
  let vx: setvar x
  assume hoaddid1.1: |- T : ~H --> ~H


  assert |- ( T +op 0hop ) = T

  proof
    vx
    cv
    #
    cT
    ch0o
    chos
    co
    #
    cfv
    #
    @0
    cT
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @1
    cT
    wceq
    @4
    vx
    chil
    @0
    chil
    wcel
    #
    @2
    @3
    @0
    ch0o
    cfv
    #
    cva
    co
    #
    @3
    c0v
    cva
    co
    #
    @3
    chil
    chil
    cT
    wf
    chil
    chil
    ch0o
    wf
    @5
    @2
    @7
    wceq
    hoaddid1.1
    ho0f
    @0
    cT
    ch0o
    hosval
    mp3an12
    @5
    @6
    c0v
    @3
    cva
    @0
    ho0val
    oveq2d
    @5
    @3
    chil
    wcel
    @8
    @3
    wceq
    chil
    chil
    @0
    cT
    hoaddid1.1
    ffvelrni
    @3
    ax-hvaddid
    syl
    3eqtrd
    rgen
    vx
    @1
    cT
    cT
    ch0o
    hoaddid1.1
    ho0f
    hoaddcli
    hoaddid1.1
    hoeqi
    mpbi
end
