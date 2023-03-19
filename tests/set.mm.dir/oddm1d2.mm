include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "oddp1d2.mm"
include "zob.mm"
include "bitrd.mm"

theorem oddm1d2
  let cN: class N


  assert |- ( N e. ZZ -> ( -. 2 || N <-> ( ( N - 1 ) / 2 ) e. ZZ ) )

  proof
    cN
    cz
    wcel
    c2
    cN
    cdvds
    wbr
    wn
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cz
    wcel
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    cz
    wcel
    cN
    oddp1d2
    cN
    zob
    bitrd
end
