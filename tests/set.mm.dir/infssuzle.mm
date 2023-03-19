include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "uzwo.mm"
include "sylan2.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "sstr.mm"
include "mpan2.mm"
include "lbinfle.mm"
include "3com23.mm"
include "syl3an1.mm"
include "mpd3an3.mm"

theorem infssuzle
  let cA: class A
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vj: setvar j


  assert |- ( ( S C_ ( ZZ>= ` M ) /\ A e. S ) -> inf ( S , RR , < ) <_ A )

  proof
    cS
    cM
    cuz
    cfv
    #
    wss
    #
    cA
    cS
    wcel
    #
    vj
    cv
    vk
    cv
    cle
    wbr
    vk
    cS
    wral
    vj
    cS
    wrex
    #
    cS
    cr
    clt
    cinf
    cA
    cle
    wbr
    #
    @2
    @1
    cS
    c0
    wne
    @3
    cS
    cA
    ne0i
    cS
    vj
    vk
    cM
    uzwo
    sylan2
    @1
    cS
    cr
    wss
    #
    @2
    @3
    @4
    @1
    @0
    cr
    wss
    @5
    @0
    cz
    cr
    cM
    uzssz
    zssre
    sstri
    cS
    @0
    cr
    sstr
    mpan2
    @5
    @3
    @2
    @4
    vj
    vk
    cA
    cS
    lbinfle
    3com23
    syl3an1
    mpd3an3
end
