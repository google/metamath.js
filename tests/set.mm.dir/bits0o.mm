include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cbits.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "2z.mm"
include "dvdsmul1.mm"
include "mpan.mm"
include "cn.mm"
include "clt.mm"
include "wi.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "2nn.mm"
include "1lt2.mm"
include "ndvdsp1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "wb.mm"
include "peano2zd.mm"
include "bits0.mm"
include "syl.mm"
include "mpbird.mm"

theorem bits0o
  let cN: class N


  assert |- ( N e. ZZ -> 0 e. ( bits ` ( ( 2 x. N ) + 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    cbits
    cfv
    wcel
    #
    c2
    @2
    cdvds
    wbr
    wn
    #
    @0
    c2
    @1
    cdvds
    wbr
    #
    @4
    c2
    cz
    wcel
    #
    @0
    @5
    2z
    c2
    cN
    dvdsmul1
    mpan
    @0
    @1
    cz
    wcel
    c2
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @5
    @4
    wi
    @0
    c2
    cN
    @6
    @0
    2z
    a1i
    @0
    id
    zmulcld
    #
    @7
    @0
    2nn
    a1i
    @8
    @0
    1lt2
    a1i
    c2
    @1
    ndvdsp1
    syl3anc
    mpd
    @0
    @2
    cz
    wcel
    @3
    @4
    wb
    @0
    @1
    @9
    peano2zd
    @2
    bits0
    syl
    mpbird
end
