include "cfzo.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "elfzolt2.mm"
include "adantr.mm"
include "cle.mm"
include "wn.mm"
include "eluzle.mm"
include "adantl.mm"
include "cz.mm"
include "eluzel2.mm"
include "zred.mm"
include "cr.mm"
include "eluzelre.mm"
include "lenltd.mm"
include "mpbid.mm"
include "pm2.65i.mm"
include "elin.mm"
include "mtbir.mm"
include "nel0.mm"

theorem fzouzdisj
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C
  let cD: class D


  assert |- ( ( A ..^ B ) i^i ( ZZ>= ` B ) ) = (/)

  proof
    vx
    cA
    cB
    cfzo
    co
    #
    cB
    cuz
    cfv
    #
    cin
    #
    vx
    cv
    #
    @2
    wcel
    @3
    @0
    wcel
    #
    @3
    @1
    wcel
    #
    wa
    #
    @6
    @3
    cB
    clt
    wbr
    #
    @4
    @7
    @5
    @3
    cA
    cB
    elfzolt2
    adantr
    @6
    cB
    @3
    cle
    wbr
    #
    @7
    wn
    @5
    @8
    @4
    cB
    @3
    eluzle
    adantl
    @6
    cB
    @3
    @6
    cB
    @5
    cB
    cz
    wcel
    @4
    cB
    @3
    eluzel2
    adantl
    zred
    @5
    @3
    cr
    wcel
    @4
    cB
    @3
    eluzelre
    adantl
    lenltd
    mpbid
    pm2.65i
    @3
    @0
    @1
    elin
    mtbir
    nel0
end
