include "cpw.mm"
include "crpss.mm"
include "ccnv.mm"
include "whe.mm"
include "cid.mm"
include "cun.mm"
include "psshepw.mm"
include "idhe.mm"
include "unhe1.mm"
include "mp2an.mm"

theorem sshepw
  let cA: class A


  assert |- ( `' [C.] u. _I ) hereditary ~P A

  proof
    cA
    cpw
    #
    crpss
    ccnv
    #
    whe
    @0
    cid
    whe
    @0
    @1
    cid
    cun
    whe
    cA
    psshepw
    @0
    idhe
    @0
    @1
    cid
    unhe1
    mp2an
end
