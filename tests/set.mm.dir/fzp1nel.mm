include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "wn.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cr.mm"
include "zre.mm"
include "clt.mm"
include "ltp1.mm"
include "id.mm"
include "peano2re.mm"
include "ltnled.mm"
include "mpbid.mm"
include "syl.mm"
include "intnand.mm"
include "3ad2ant2.mm"
include "elfz2.mm"
include "notbii.mm"
include "imnan.mm"
include "bitr4i.mm"
include "mpbir.mm"

theorem fzp1nel
  let cM: class M
  let cN: class N


  assert |- -. ( N + 1 ) e. ( M ... N )

  proof
    cN
    c1
    caddc
    co
    #
    cM
    cN
    cfz
    co
    wcel
    #
    wn
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    w3a
    #
    cM
    @0
    cle
    wbr
    #
    @0
    cN
    cle
    wbr
    #
    wa
    #
    wn
    #
    wi
    #
    @4
    @3
    @10
    @5
    @4
    @8
    @7
    @4
    cN
    cr
    wcel
    #
    @8
    wn
    #
    cN
    zre
    @12
    cN
    @0
    clt
    wbr
    @13
    cN
    ltp1
    @12
    cN
    @0
    @12
    id
    cN
    peano2re
    ltnled
    mpbid
    syl
    intnand
    3ad2ant2
    @2
    @6
    @9
    wa
    #
    wn
    @11
    @1
    @14
    @0
    cM
    cN
    elfz2
    notbii
    @6
    @9
    imnan
    bitr4i
    mpbir
end
