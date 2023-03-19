include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cuz.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "zex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "rgenw.mm"
include "df-uz.mm"
include "fmpt.mm"
include "mpbi.mm"

theorem uzf
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  let cM: class M


  assert |- ZZ>= : ZZ --> ~P ZZ

  proof
    vj
    cv
    vk
    cv
    cle
    wbr
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
    vj
    cz
    wral
    cz
    @2
    cuz
    wf
    @3
    vj
    cz
    @3
    @1
    cz
    wss
    @0
    vk
    cz
    ssrab2
    @1
    cz
    zex
    elpw2
    mpbir
    rgenw
    vj
    cz
    @2
    @1
    cuz
    vj
    vk
    df-uz
    fmpt
    mpbi
end
