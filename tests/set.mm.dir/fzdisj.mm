include "clt.mm"
include "wbr.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "elin.mm"
include "cle.mm"
include "cz.mm"
include "elfzel1.mm"
include "adantl.mm"
include "zred.mm"
include "cr.mm"
include "elfzelz.mm"
include "elfzel2.mm"
include "adantr.mm"
include "elfzle1.mm"
include "elfzle2.mm"
include "letrd.mm"
include "lenltd.mm"
include "mpbid.mm"
include "sylbi.mm"
include "con2i.mm"
include "eq0rdv.mm"

theorem fzdisj
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( K < M -> ( ( J ... K ) i^i ( M ... N ) ) = (/) )

  proof
    cK
    cM
    clt
    wbr
    #
    vx
    cJ
    cK
    cfz
    co
    #
    cM
    cN
    cfz
    co
    #
    cin
    #
    vx
    cv
    #
    @3
    wcel
    #
    @0
    @5
    @4
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    wa
    #
    @0
    wn
    #
    @4
    @1
    @2
    elin
    @8
    cM
    cK
    cle
    wbr
    @9
    @8
    cM
    @4
    cK
    @8
    cM
    @7
    cM
    cz
    wcel
    @6
    @4
    cM
    cN
    elfzel1
    adantl
    zred
    #
    @7
    @4
    cr
    wcel
    @6
    @7
    @4
    @4
    cM
    cN
    elfzelz
    zred
    adantl
    @8
    cK
    @6
    cK
    cz
    wcel
    @7
    @4
    cJ
    cK
    elfzel2
    adantr
    zred
    #
    @7
    cM
    @4
    cle
    wbr
    @6
    @4
    cM
    cN
    elfzle1
    adantl
    @6
    @4
    cK
    cle
    wbr
    @7
    @4
    cJ
    cK
    elfzle2
    adantr
    letrd
    @8
    cM
    cK
    @10
    @11
    lenltd
    mpbid
    sylbi
    con2i
    eq0rdv
end
