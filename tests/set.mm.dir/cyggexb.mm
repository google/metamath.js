include "cabl.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "ccyg.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cyggex.mm"
include "expcom.mm"
include "adantl.mm"
include "cv.mm"
include "cod.mm"
include "wrex.mm"
include "cn.mm"
include "simpll.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "gexcl2.mm"
include "syl2anc.mm"
include "eqid.mm"
include "gexex.mm"
include "eqeq2d.mm"
include "cz.mm"
include "cmg.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "crab.mm"
include "wb.mm"
include "cyggenod.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "iscyg2.mm"
include "baib.mm"
include "syl.mm"
include "syl5ibr.mm"
include "sylbird.mm"
include "expdimp.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "impbid.mm"

theorem cyggexb
  let cB: class B
  let cE: class E
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )
  assume cyggex.o: |- E = ( gEx ` G )


  assert |- ( ( G e. Abel /\ B e. Fin ) -> ( G e. CycGrp <-> E = ( # ` B ) ) )

  proof
    cG
    cabl
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cG
    ccyg
    wcel
    #
    cE
    cB
    chash
    cfv
    #
    wceq
    #
    @1
    @3
    @5
    wi
    @0
    @3
    @1
    @5
    cB
    cE
    cG
    cygctb.1
    cyggex.o
    cyggex
    expcom
    adantl
    @2
    @5
    @3
    @2
    @5
    wa
    #
    vx
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    #
    cE
    wceq
    #
    vx
    cB
    wrex
    #
    @3
    @6
    @0
    cE
    cn
    wcel
    #
    @11
    @0
    @1
    @5
    simpll
    @6
    cG
    cgrp
    wcel
    #
    @1
    @12
    @0
    @13
    @1
    @5
    cG
    ablgrp
    ad2antrr
    #
    @0
    @1
    @5
    simplr
    #
    cE
    cG
    cB
    cygctb.1
    cyggex.o
    gexcl2
    syl2anc
    vx
    cE
    cG
    @8
    cB
    cygctb.1
    cyggex.o
    @8
    eqid
    #
    gexex
    syl2anc
    @6
    @10
    @3
    vx
    cB
    @6
    @7
    cB
    wcel
    #
    wa
    #
    @10
    @9
    @4
    wceq
    #
    @3
    @18
    cE
    @4
    @9
    @2
    @5
    @17
    simplr
    eqeq2d
    @6
    @17
    @19
    @3
    @6
    @17
    @19
    wa
    #
    @7
    vn
    cz
    vn
    cv
    vy
    cv
    cG
    cmg
    cfv
    #
    co
    cmpt
    crn
    cB
    wceq
    vy
    cB
    crab
    #
    wcel
    #
    @3
    @6
    @13
    @1
    @23
    @20
    wb
    @14
    @15
    vy
    cB
    @21
    vn
    @22
    cG
    @8
    @7
    cygctb.1
    @21
    eqid
    #
    @22
    eqid
    #
    @16
    cyggenod
    syl2anc
    @23
    @3
    @6
    @22
    c0
    wne
    #
    @22
    @7
    ne0i
    @6
    @13
    @3
    @26
    wb
    @14
    @3
    @13
    @26
    vy
    cB
    @21
    vn
    @22
    cG
    cygctb.1
    @24
    @25
    iscyg2
    baib
    syl
    syl5ibr
    sylbird
    expdimp
    sylbid
    rexlimdva
    mpd
    ex
    impbid
end
