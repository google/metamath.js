include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cle.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "adantl.mm"
include "exprmfct.mm"
include "syl.mm"
include "cz.mm"
include "wi.mm"
include "prmz.mm"
include "eluz2nn.mm"
include "dvdsle.mm"
include "syl2anr.mm"
include "elfzle2.mm"
include "ad2antlr.mm"
include "cr.mm"
include "zred.mm"
include "elfzelz.mm"
include "nnre.mm"
include "ad2antrr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syld.mm"
include "ancrd.mm"
include "reximdva.mm"
include "mpd.mm"

theorem prmdvdsfz
  let cI: class I
  let cN: class N
  let vp: setvar p

  disjoint I p
  disjoint N p
  assert |- ( ( N e. NN /\ I e. ( 2 ... N ) ) -> E. p e. Prime ( p <_ N /\ p || I ) )

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
    cI
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @3
    cN
    cle
    wbr
    #
    @4
    wa
    #
    vp
    cprime
    wrex
    @2
    cI
    c2
    cuz
    cfv
    wcel
    #
    @5
    @1
    @8
    @0
    cI
    c2
    cN
    elfzuz
    #
    adantl
    cI
    vp
    exprmfct
    syl
    @2
    @4
    @7
    vp
    cprime
    @2
    @3
    cprime
    wcel
    #
    wa
    #
    @4
    @6
    @11
    @4
    @3
    cI
    cle
    wbr
    #
    @6
    @10
    @3
    cz
    wcel
    cI
    cn
    wcel
    #
    @4
    @12
    wi
    @2
    @3
    prmz
    #
    @1
    @13
    @0
    @1
    @8
    @13
    @9
    cI
    eluz2nn
    syl
    adantl
    @3
    cI
    dvdsle
    syl2anr
    @11
    @12
    cI
    cN
    cle
    wbr
    #
    @6
    @1
    @15
    @0
    @10
    cI
    c2
    cN
    elfzle2
    ad2antlr
    @11
    @3
    cr
    wcel
    #
    cI
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @12
    @15
    wa
    @6
    wi
    @10
    @16
    @2
    @10
    @3
    @14
    zred
    adantl
    @1
    @17
    @0
    @10
    @1
    cI
    cI
    c2
    cN
    elfzelz
    zred
    ad2antlr
    @0
    @18
    @1
    @10
    cN
    nnre
    ad2antrr
    @3
    cI
    cN
    letr
    syl3anc
    mpan2d
    syld
    ancrd
    reximdva
    mpd
end
