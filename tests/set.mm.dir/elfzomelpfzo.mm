include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "cfzo.mm"
include "cle.mm"
include "zsubcl.mm"
include "ad2ant2rl.mm"
include "simpl.mm"
include "adantr.mm"
include "2thd.mm"
include "adantl.mm"
include "zaddcl.mm"
include "cr.mm"
include "zre.mm"
include "lesubaddd.mm"
include "3anbi123d.mm"
include "eluz2.mm"
include "3bitr4g.mm"
include "ad2ant2l.mm"
include "simplr.mm"
include "ltaddsubd.mm"
include "bicomd.mm"
include "elfzo2.mm"

theorem elfzomelpfzo
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( K e. ZZ /\ L e. ZZ ) ) -> ( K e. ( ( M - L ) ..^ ( N - L ) ) <-> ( K + L ) e. ( M ..^ N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cK
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    wa
    #
    wa
    #
    cK
    cM
    cL
    cmin
    co
    #
    cuz
    cfv
    wcel
    #
    cN
    cL
    cmin
    co
    #
    cz
    wcel
    #
    cK
    @9
    clt
    wbr
    #
    w3a
    cK
    cL
    caddc
    co
    #
    cM
    cuz
    cfv
    wcel
    #
    @1
    @12
    cN
    clt
    wbr
    #
    w3a
    cK
    @7
    @9
    cfzo
    co
    wcel
    @12
    cM
    cN
    cfzo
    co
    wcel
    @6
    @8
    @13
    @10
    @1
    @11
    @14
    @6
    @7
    cz
    wcel
    #
    @3
    @7
    cK
    cle
    wbr
    #
    w3a
    @0
    @12
    cz
    wcel
    #
    cM
    @12
    cle
    wbr
    #
    w3a
    @8
    @13
    @6
    @15
    @0
    @3
    @17
    @16
    @18
    @6
    @15
    @0
    @0
    @4
    @15
    @1
    @3
    cM
    cL
    zsubcl
    ad2ant2rl
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    2thd
    @6
    @3
    @17
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @5
    @17
    @2
    cK
    cL
    zaddcl
    adantl
    2thd
    @6
    cM
    cL
    cK
    @2
    cM
    cr
    wcel
    #
    @5
    @0
    @19
    @1
    cM
    zre
    adantr
    adantr
    @5
    cL
    cr
    wcel
    #
    @2
    @4
    @20
    @3
    cL
    zre
    adantl
    adantl
    #
    @5
    cK
    cr
    wcel
    #
    @2
    @3
    @22
    @4
    cK
    zre
    adantr
    adantl
    #
    lesubaddd
    3anbi123d
    @7
    cK
    eluz2
    cM
    @12
    eluz2
    3bitr4g
    @6
    @10
    @1
    @1
    @4
    @10
    @0
    @3
    cN
    cL
    zsubcl
    ad2ant2l
    @0
    @1
    @5
    simplr
    2thd
    @6
    @14
    @11
    @6
    cK
    cL
    cN
    @23
    @21
    @2
    cN
    cr
    wcel
    #
    @5
    @1
    @24
    @0
    cN
    zre
    adantl
    adantr
    ltaddsubd
    bicomd
    3anbi123d
    cK
    @7
    @9
    elfzo2
    @12
    cM
    cN
    elfzo2
    3bitr4g
end
