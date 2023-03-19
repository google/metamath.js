include "cc.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "cabs.mm"
include "cre.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "ci.mm"
include "cim.mm"
include "caddc.mm"
include "replim.mm"
include "fveq2d.mm"
include "wceq.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "reefcld.mm"
include "efcl.mm"
include "syl.mm"
include "absmuld.mm"
include "cr.mm"
include "absefi.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "abscld.mm"
include "mulid1d.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "efgt0.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpd.mm"
include "absidd.mm"

theorem absef
  let cA: class A


  assert |- ( A e. CC -> ( abs ` ( exp ` A ) ) = ( exp ` ( Re ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ce
    cfv
    #
    cabs
    cfv
    #
    cA
    cre
    cfv
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    c1
    cmul
    co
    #
    @5
    @4
    @0
    @2
    @4
    ci
    cA
    cim
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    cabs
    cfv
    @5
    @9
    cabs
    cfv
    #
    cmul
    co
    @6
    @0
    @1
    @10
    cabs
    @0
    @1
    @3
    @8
    caddc
    co
    #
    ce
    cfv
    #
    @10
    @0
    cA
    @12
    ce
    cA
    replim
    fveq2d
    @0
    @3
    cc
    wcel
    @8
    cc
    wcel
    #
    @13
    @10
    wceq
    @0
    @3
    cA
    recl
    #
    recnd
    @0
    ci
    cc
    wcel
    @7
    cc
    wcel
    @14
    ax-icn
    @0
    @7
    cA
    imcl
    #
    recnd
    ci
    @7
    mulcl
    sylancr
    #
    @3
    @8
    efadd
    syl2anc
    eqtrd
    fveq2d
    @0
    @4
    @9
    @0
    @4
    @0
    @3
    @15
    reefcld
    #
    recnd
    #
    @0
    @14
    @9
    cc
    wcel
    @17
    @8
    efcl
    syl
    absmuld
    @0
    @11
    c1
    @5
    cmul
    @0
    @7
    cr
    wcel
    @11
    c1
    wceq
    @16
    @7
    absefi
    syl
    oveq2d
    3eqtrd
    @0
    @5
    @0
    @5
    @0
    @4
    @19
    abscld
    recnd
    mulid1d
    @0
    @4
    @18
    @0
    cc0
    @4
    clt
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @0
    @3
    cr
    wcel
    @20
    @15
    @3
    efgt0
    syl
    @0
    cc0
    cr
    wcel
    @4
    cr
    wcel
    @20
    @21
    wi
    0re
    @18
    cc0
    @4
    ltle
    sylancr
    mpd
    absidd
    3eqtrd
end
