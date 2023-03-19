include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "crab.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cfz.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "zex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "rgen2w.mm"
include "df-fz.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem fzf
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  let cN: class N


  assert |- ... : ( ZZ X. ZZ ) --> ~P ZZ

  proof
    vm
    cv
    vk
    cv
    #
    cle
    wbr
    @0
    vn
    cv
    cle
    wbr
    wa
    #
    vk
    cz
    crab
    #
    cz
    cpw
    #
    wcel
    #
    vn
    cz
    wral
    vm
    cz
    wral
    cz
    cz
    cxp
    @3
    cfz
    wf
    @4
    vm
    vn
    cz
    cz
    @4
    @2
    cz
    wss
    @1
    vk
    cz
    ssrab2
    @2
    cz
    zex
    elpw2
    mpbir
    rgen2w
    vm
    vn
    cz
    cz
    @2
    @3
    cfz
    vk
    vm
    vn
    df-fz
    fmpt2
    mpbi
end
