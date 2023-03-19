include "cz.mm"
include "cn0.mm"
include "cpw.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cbits.mm"
include "df-bits.mm"
include "wcel.mm"
include "wss.mm"
include "ssrab2.mm"
include "nn0ex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "a1i.mm"
include "fmpti.mm"

theorem bitsf
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let vm: setvar m
  let cN: class N


  assert |- bits : ZZ --> ~P NN0

  proof
    vn
    cz
    cn0
    cpw
    #
    c2
    vn
    cv
    #
    c2
    vk
    cv
    cexp
    co
    cdiv
    co
    cfl
    cfv
    cdvds
    wbr
    wn
    #
    vk
    cn0
    crab
    #
    cbits
    vk
    vn
    df-bits
    @3
    @0
    wcel
    #
    @1
    cz
    wcel
    @4
    @3
    cn0
    wss
    @2
    vk
    cn0
    ssrab2
    @3
    cn0
    nn0ex
    elpw2
    mpbir
    a1i
    fmpti
end
