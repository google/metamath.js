include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "cprime.mm"
include "wrex.mm"
include "cprmo.mm"
include "cfv.mm"
include "caddc.mm"
include "w3a.mm"
include "prmdvdsfz.mm"
include "simprl.mm"
include "simprr.mm"
include "wi.mm"
include "wral.mm"
include "prmdvdsprmo.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl5com.mm"
include "adantr.mm"
include "imp.mm"
include "adantrd.mm"
include "cz.mm"
include "prmz.mm"
include "ad2antlr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "prmocl.mm"
include "syl.mm"
include "nnzd.mm"
include "elfzelz.mm"
include "dvds2add.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "3jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem prmdvdsprmop
  let cI: class I
  let cN: class N
  let vp: setvar p
  let vq: setvar q

  disjoint I p
  disjoint N p
  disjoint N q
  disjoint p q
  assert |- ( ( N e. NN /\ I e. ( 2 ... N ) ) -> E. p e. Prime ( p <_ N /\ p || I /\ p || ( ( #p ` N ) + I ) ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c2
    cN
    cfz
    co
    wcel
    #
    wa
    #
    vp
    cv
    #
    cN
    cle
    wbr
    #
    @3
    cI
    cdvds
    wbr
    #
    wa
    #
    vp
    cprime
    wrex
    @4
    @5
    @3
    cN
    cprmo
    cfv
    #
    cI
    caddc
    co
    cdvds
    wbr
    #
    w3a
    #
    vp
    cprime
    wrex
    cI
    cN
    vp
    prmdvdsfz
    @2
    @6
    @9
    vp
    cprime
    @2
    @3
    cprime
    wcel
    #
    wa
    #
    @6
    @9
    @11
    @6
    wa
    #
    @4
    @5
    @8
    @11
    @4
    @5
    simprl
    @11
    @4
    @5
    simprr
    #
    @12
    @3
    @7
    cdvds
    wbr
    #
    @5
    @8
    @11
    @6
    @14
    @11
    @4
    @14
    @5
    @2
    @10
    @4
    @14
    wi
    #
    @0
    @10
    @15
    wi
    @1
    @0
    vq
    cv
    #
    cN
    cle
    wbr
    #
    @16
    @7
    cdvds
    wbr
    #
    wi
    #
    vq
    cprime
    wral
    @10
    @15
    cN
    vq
    prmdvdsprmo
    @19
    @15
    vq
    @3
    cprime
    @16
    @3
    wceq
    @17
    @4
    @18
    @14
    @16
    @3
    cN
    cle
    breq1
    @16
    @3
    @7
    cdvds
    breq1
    imbi12d
    rspcv
    syl5com
    adantr
    imp
    adantrd
    imp
    @13
    @12
    @3
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    cI
    cz
    wcel
    #
    @14
    @5
    wa
    @8
    wi
    @10
    @20
    @2
    @6
    @3
    prmz
    ad2antlr
    @11
    @21
    @6
    @2
    @21
    @10
    @0
    @21
    @1
    @0
    @7
    @0
    cN
    cn0
    wcel
    @7
    cn
    wcel
    cN
    nnnn0
    cN
    prmocl
    syl
    nnzd
    adantr
    adantr
    adantr
    @11
    @22
    @6
    @1
    @22
    @0
    @10
    cI
    c2
    cN
    elfzelz
    ad2antlr
    adantr
    @3
    @7
    cI
    dvds2add
    syl3anc
    mp2and
    3jca
    ex
    reximdva
    mpd
end
