include "wel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "cv.mm"
include "wtr.mm"
include "cep.mm"
include "wpo.mm"
include "alral.mm"
include "alimi.mm"
include "syl.mm"
include "ralimi.mm"
include "ralcom.mm"
include "ralbii.mm"
include "bitri.mm"
include "sylib.mm"
include "dftr2.mm"
include "wbr.mm"
include "wn.mm"
include "df-po.mm"
include "epel.mm"
include "anbi12i.mm"
include "imbi12i.mm"
include "elirrv.mm"
include "mtbir.mm"
include "biantrur.mm"
include "bitr3i.mm"
include "2ralbii.mm"
include "bitr4i.mm"
include "3imtr4i.mm"

theorem elpotr
  let vz: setvar z
  let cA: class A
  let vx: setvar x
  let vy: setvar y

  disjoint A z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  assert |- ( A. z e. A Tr z -> _E Po A )

  proof
    vx
    vy
    wel
    #
    vy
    vz
    wel
    #
    wa
    #
    vx
    vz
    wel
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    vz
    cA
    wral
    #
    @4
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    vz
    cv
    #
    wtr
    #
    vz
    cA
    wral
    cA
    cep
    wpo
    #
    @7
    @4
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    vz
    cA
    wral
    #
    @10
    @6
    @15
    vz
    cA
    @6
    @14
    vx
    wal
    @15
    @5
    @14
    vx
    @4
    vy
    cA
    alral
    alimi
    @14
    vx
    cA
    alral
    syl
    ralimi
    @16
    @14
    vz
    cA
    wral
    #
    vx
    cA
    wral
    @10
    @14
    vz
    vx
    cA
    cA
    ralcom
    @17
    @9
    vx
    cA
    @4
    vz
    vy
    cA
    cA
    ralcom
    ralbii
    bitri
    sylib
    @12
    @6
    vz
    cA
    vx
    vy
    @11
    dftr2
    ralbii
    @13
    vx
    cv
    #
    @18
    cep
    wbr
    #
    wn
    #
    @18
    vy
    cv
    #
    cep
    wbr
    #
    @21
    @11
    cep
    wbr
    #
    wa
    #
    @18
    @11
    cep
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @10
    vx
    vy
    vz
    cA
    cep
    df-po
    @8
    @28
    vx
    vy
    cA
    cA
    @4
    @27
    vz
    cA
    @4
    @26
    @27
    @24
    @2
    @25
    @3
    @22
    @0
    @23
    @1
    vx
    vy
    epel
    vy
    vz
    epel
    anbi12i
    vx
    vz
    epel
    imbi12i
    @20
    @26
    @19
    vx
    vx
    wel
    vx
    elirrv
    vx
    vx
    epel
    mtbir
    biantrur
    bitr3i
    ralbii
    2ralbii
    bitr4i
    3imtr4i
end
