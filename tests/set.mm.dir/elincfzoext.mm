include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wi.mm"
include "elfzole1.mm"
include "cr.mm"
include "elfzoelz.mm"
include "zred.mm"
include "adantr.mm"
include "nn0addge1.mm"
include "sylan.mm"
include "elfzoel1.mm"
include "nn0re.mm"
include "adantl.mm"
include "readdcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "exp4b.mm"
include "com23.mm"
include "imp31.mm"
include "mpd.mm"
include "exp31.mm"
include "imp.mm"
include "elfzoel2.mm"
include "elfzolt2.mm"
include "ltadd1dd.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "zaddcld.mm"
include "elfzo.mm"
include "mpbir2and.mm"

theorem elincfzoext
  let cI: class I
  let cM: class M
  let cN: class N
  let cZ: class Z


  assert |- ( ( Z e. ( M ..^ N ) /\ I e. NN0 ) -> ( Z + I ) e. ( M ..^ ( N + I ) ) )

  proof
    cZ
    cM
    cN
    cfzo
    co
    wcel
    #
    cI
    cn0
    wcel
    #
    wa
    #
    cZ
    cI
    caddc
    co
    #
    cM
    cN
    cI
    caddc
    co
    #
    cfzo
    co
    wcel
    #
    cM
    @3
    cle
    wbr
    #
    @3
    @4
    clt
    wbr
    #
    @0
    @1
    @6
    @0
    cM
    cZ
    cle
    wbr
    #
    @1
    @6
    wi
    cZ
    cM
    cN
    elfzole1
    @0
    @8
    @1
    @6
    @0
    @8
    wa
    #
    @1
    wa
    cZ
    @3
    cle
    wbr
    #
    @6
    @9
    cZ
    cr
    wcel
    #
    @1
    @10
    @0
    @11
    @8
    @0
    cZ
    cZ
    cM
    cN
    elfzoelz
    #
    zred
    #
    adantr
    cZ
    cI
    nn0addge1
    sylan
    @0
    @8
    @1
    @10
    @6
    wi
    #
    @0
    @1
    @8
    @14
    @0
    @1
    @8
    @10
    @6
    @2
    cM
    cr
    wcel
    #
    @11
    @3
    cr
    wcel
    @8
    @10
    wa
    @6
    wi
    @0
    @15
    @1
    @0
    cM
    cZ
    cM
    cN
    elfzoel1
    #
    zred
    adantr
    @0
    @11
    @1
    @13
    adantr
    #
    @2
    cZ
    cI
    @17
    @1
    cI
    cr
    wcel
    @0
    cI
    nn0re
    adantl
    #
    readdcld
    cM
    cZ
    @3
    letr
    syl3anc
    exp4b
    com23
    imp31
    mpd
    exp31
    mpd
    imp
    @2
    cZ
    cN
    cI
    @17
    @0
    cN
    cr
    wcel
    @1
    @0
    cN
    cZ
    cM
    cN
    elfzoel2
    #
    zred
    adantr
    @18
    @0
    cZ
    cN
    clt
    wbr
    @1
    cZ
    cM
    cN
    elfzolt2
    adantr
    ltadd1dd
    @2
    @3
    cz
    wcel
    cM
    cz
    wcel
    #
    @4
    cz
    wcel
    @5
    @6
    @7
    wa
    wb
    @2
    cZ
    cI
    @0
    cZ
    cz
    wcel
    @1
    @12
    adantr
    @1
    cI
    cz
    wcel
    @0
    cI
    nn0z
    adantl
    #
    zaddcld
    @0
    @20
    @1
    @16
    adantr
    @2
    cN
    cI
    @0
    cN
    cz
    wcel
    @1
    @19
    adantr
    @21
    zaddcld
    @3
    cM
    @4
    elfzo
    syl3anc
    mpbir2and
end
