include "crng.mm"
include "wcel.mm"
include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgmhm.mm"
include "crngh.mm"
include "wss.mm"
include "ringssrng.mm"
include "a1i.mm"
include "ssdifssd.mm"
include "sseld.mm"
include "imdistani.mm"
include "cgrp.mm"
include "cabl.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "eldifi.mm"
include "ringgrp.mm"
include "c0ghm.mm"
include "syl2an.mm"
include "cur.mm"
include "cmpt.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "0ring1eq0.mm"
include "eqcomd.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "syl5eq.mm"
include "cmgm.mm"
include "cmnd.mm"
include "csgrp.mm"
include "rngmgp.mm"
include "sgrpmgm.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "c0mgm.mm"
include "eqeltrd.mm"
include "jca.mm"
include "isrnghmmul.mm"
include "sylanbrc.mm"

theorem c0rnghm
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cT: class T
  let cH: class H
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume c0mhm.b: |- B = ( Base ` S )
  assume c0mhm.0: |- .0. = ( 0g ` T )
  assume c0mhm.h: |- H = ( x e. B |-> .0. )

  disjoint B x
  disjoint S x
  disjoint T x
  disjoint .0. x
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint H a
  disjoint H b
  disjoint S a
  disjoint S b
  disjoint T a
  disjoint T b
  disjoint k x
  assert |- ( ( S e. Rng /\ T e. ( Ring \ NzRing ) ) -> H e. ( S RngHomo T ) )

  proof
    cS
    crng
    wcel
    #
    cT
    crg
    cnzr
    cdif
    #
    wcel
    #
    wa
    #
    @0
    cT
    crng
    wcel
    #
    wa
    cH
    cS
    cT
    cghm
    co
    wcel
    #
    cH
    cS
    cmgp
    cfv
    #
    cT
    cmgp
    cfv
    #
    cmgmhm
    co
    #
    wcel
    #
    wa
    cH
    cS
    cT
    crngh
    co
    wcel
    @0
    @2
    @4
    @0
    @1
    crng
    cT
    @0
    crg
    crng
    cnzr
    crg
    crng
    wss
    @0
    ringssrng
    a1i
    ssdifssd
    sseld
    imdistani
    @3
    @5
    @9
    @0
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    @5
    @2
    @0
    cS
    cabl
    wcel
    @10
    cS
    rngabl
    cS
    ablgrp
    syl
    @2
    cT
    crg
    wcel
    #
    @11
    cT
    crg
    cnzr
    eldifi
    #
    cT
    ringgrp
    syl
    vx
    cB
    cS
    cT
    cH
    c.0
    c0mhm.b
    c0mhm.0
    c0mhm.h
    c0ghm
    syl2an
    @3
    cH
    vx
    cB
    cT
    cur
    cfv
    #
    cmpt
    #
    @8
    @3
    cH
    vx
    cB
    c.0
    cmpt
    #
    @15
    c0mhm.h
    @2
    @16
    @15
    wceq
    @0
    @2
    vx
    cB
    c.0
    @14
    @2
    @14
    c.0
    cT
    cbs
    cfv
    #
    cT
    @14
    c.0
    @17
    eqid
    c0mhm.0
    @14
    eqid
    #
    0ring1eq0
    eqcomd
    mpteq2dv
    adantl
    syl5eq
    @0
    @6
    cmgm
    wcel
    #
    @7
    cmnd
    wcel
    #
    @15
    @8
    wcel
    @2
    @0
    @6
    csgrp
    wcel
    @19
    cS
    @6
    @6
    eqid
    #
    rngmgp
    @6
    sgrpmgm
    syl
    @2
    @12
    @20
    @13
    cT
    @7
    @7
    eqid
    #
    ringmgp
    syl
    vx
    cB
    @6
    @7
    @15
    @14
    cB
    cS
    @6
    @21
    c0mhm.b
    mgpbas
    cT
    @14
    @7
    @22
    @18
    ringidval
    @15
    eqid
    c0mgm
    syl2an
    eqeltrd
    jca
    cS
    cT
    cH
    @6
    @7
    @21
    @22
    isrnghmmul
    sylanbrc
end
