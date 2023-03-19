include "cc0.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wnel.mm"
include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "clt.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "intnanr.mm"
include "intnan.mm"
include "df-nel.mm"
include "elfz2.mm"
include "xchbinx.mm"
include "mpbir.mm"

theorem 0nelfz1
  let cN: class N


  assert |- 0 e/ ( 1 ... N )

  proof
    cc0
    c1
    cN
    cfz
    co
    #
    wnel
    #
    c1
    cz
    wcel
    cN
    cz
    wcel
    cc0
    cz
    wcel
    w3a
    #
    c1
    cc0
    cle
    wbr
    #
    cc0
    cN
    cle
    wbr
    #
    wa
    #
    wa
    #
    wn
    @5
    @2
    @3
    @4
    cc0
    c1
    clt
    wbr
    @3
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnlei
    mpbi
    intnanr
    intnan
    @1
    cc0
    @0
    wcel
    @6
    cc0
    @0
    df-nel
    cc0
    c1
    cN
    elfz2
    xchbinx
    mpbir
end
