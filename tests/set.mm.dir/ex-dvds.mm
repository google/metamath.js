include "c2.mm"
include "cz.mm"
include "wcel.mm"
include "c3.mm"
include "c6.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "2z.mm"
include "3z.mm"
include "6nn.mm"
include "nnzi.mm"
include "3pm3.2i.mm"
include "caddc.mm"
include "3cn.mm"
include "2timesi.mm"
include "3p3e6.mm"
include "eqtri.mm"
include "dvds0lem.mm"
include "mp2an.mm"

theorem ex-dvds



  assert |- 3 || 6

  proof
    c2
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    c6
    cz
    wcel
    #
    w3a
    c2
    c3
    cmul
    co
    #
    c6
    wceq
    c3
    c6
    cdvds
    wbr
    @0
    @1
    @2
    2z
    3z
    c6
    6nn
    nnzi
    3pm3.2i
    @3
    c3
    c3
    caddc
    co
    c6
    c3
    3cn
    2timesi
    3p3e6
    eqtri
    c2
    c3
    c6
    dvds0lem
    mp2an
end
