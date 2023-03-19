include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "zre.mm"
include "uzid.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "w3a.mm"
include "wi.mm"
include "eluz2.mm"
include "wa.mm"
include "adantr.mm"
include "adantl.mm"
include "lenltd.mm"
include "biimp3a.mm"
include "a1d.mm"
include "sylbi.mm"
include "impcom.mm"
include "infmin.mm"
include "ax-mp.mm"

theorem uzinfi
  let cM: class M
  let vk: setvar k
  assume uzinfi.1: |- M e. ZZ


  assert |- inf ( ( ZZ>= ` M ) , RR , < ) = M

  proof
    cM
    cz
    wcel
    #
    cM
    cuz
    cfv
    #
    cr
    clt
    cinf
    cM
    wceq
    uzinfi.1
    @0
    vk
    cr
    @1
    cM
    clt
    cr
    clt
    wor
    @0
    ltso
    a1i
    cM
    zre
    #
    cM
    uzid
    vk
    cv
    #
    @1
    wcel
    #
    @0
    @3
    cM
    clt
    wbr
    wn
    #
    @4
    @0
    @3
    cz
    wcel
    #
    cM
    @3
    cle
    wbr
    #
    w3a
    #
    @0
    @5
    wi
    cM
    @3
    eluz2
    @8
    @5
    @0
    @0
    @6
    @7
    @5
    @0
    @6
    wa
    cM
    @3
    @0
    cM
    cr
    wcel
    @6
    @2
    adantr
    @6
    @3
    cr
    wcel
    @0
    @3
    zre
    adantl
    lenltd
    biimp3a
    a1d
    sylbi
    impcom
    infmin
    ax-mp
end
