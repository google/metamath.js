include "c0.mm"
include "clcmf.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c1.mm"
include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "wnel.mm"
include "wceq.mm"
include "0ss.mm"
include "0fin.mm"
include "noel.mm"
include "nelir.mm"
include "lcmfn0val.mm"
include "mp3an.mm"
include "ral0.mm"
include "rgenw.mm"
include "rabid2.mm"
include "mpbir.mm"
include "eqcomi.mm"
include "infeq1i.mm"
include "nninf.mm"
include "3eqtri.mm"

theorem lcmf0
  let vm: setvar m
  let vn: setvar n


  assert |- ( _lcm ` (/) ) = 1

  proof
    c0
    clcmf
    cfv
    #
    vm
    cv
    vn
    cv
    cdvds
    wbr
    #
    vm
    c0
    wral
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cn
    cr
    clt
    cinf
    c1
    c0
    cz
    wss
    c0
    cfn
    wcel
    cc0
    c0
    wnel
    @0
    @4
    wceq
    cz
    0ss
    0fin
    cc0
    c0
    cc0
    noel
    nelir
    vm
    vn
    c0
    lcmfn0val
    mp3an
    cr
    @3
    cn
    clt
    cn
    @3
    cn
    @3
    wceq
    @2
    vn
    cn
    wral
    @2
    vn
    cn
    @1
    vm
    ral0
    rgenw
    @2
    vn
    cn
    rabid2
    mpbir
    eqcomi
    infeq1i
    nninf
    3eqtri
end
