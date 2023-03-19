include "c2.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "clt.mm"
include "wn.mm"
include "1lt2.mm"
include "1re.mm"
include "2re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wi.mm"
include "2z.mm"
include "1nn.mm"
include "dvdsle.mm"
include "mp2an.mm"
include "mto.mm"

theorem n2dvds1



  assert |- -. 2 || 1

  proof
    c2
    c1
    cdvds
    wbr
    #
    c2
    c1
    cle
    wbr
    #
    c1
    c2
    clt
    wbr
    @1
    wn
    1lt2
    c1
    c2
    1re
    2re
    ltnlei
    mpbi
    c2
    cz
    wcel
    c1
    cn
    wcel
    @0
    @1
    wi
    2z
    1nn
    c2
    c1
    dvdsle
    mp2an
    mto
end
