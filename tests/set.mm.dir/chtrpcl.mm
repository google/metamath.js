include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "ccht.mm"
include "cfv.mm"
include "chtcl.mm"
include "adantr.mm"
include "cc0.mm"
include "clog.mm"
include "0red.mm"
include "crp.mm"
include "c1.mm"
include "clt.mm"
include "2re.mm"
include "1lt2.mm"
include "rplogcl.mm"
include "mp2an.mm"
include "rpre.mm"
include "mp1i.mm"
include "rpgt0.mm"
include "cht2.mm"
include "chtwordi.mm"
include "mp3an1.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "elrpd.mm"

theorem chtrpcl
  let cA: class A


  assert |- ( ( A e. RR /\ 2 <_ A ) -> ( theta ` A ) e. RR+ )

  proof
    cA
    cr
    wcel
    #
    c2
    cA
    cle
    wbr
    #
    wa
    #
    cA
    ccht
    cfv
    #
    @0
    @3
    cr
    wcel
    @1
    cA
    chtcl
    adantr
    #
    @2
    cc0
    c2
    clog
    cfv
    #
    @3
    @2
    0red
    @5
    crp
    wcel
    #
    @5
    cr
    wcel
    @2
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    @6
    2re
    1lt2
    c2
    rplogcl
    mp2an
    #
    @5
    rpre
    mp1i
    @4
    @6
    cc0
    @5
    clt
    wbr
    @2
    @8
    @5
    rpgt0
    mp1i
    @2
    @5
    c2
    ccht
    cfv
    #
    @3
    cle
    cht2
    @7
    @0
    @1
    @9
    @3
    cle
    wbr
    2re
    c2
    cA
    chtwordi
    mp3an1
    syl5eqbrr
    ltletrd
    elrpd
end
