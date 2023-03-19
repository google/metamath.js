include "cvv.mm"
include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "cxp.mm"
include "cpw.mm"
include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "eleq1.mm"
include "vex.mm"
include "prsssprel.mm"
include "3exp.mm"
include "com13.mm"
include "mp2an.mm"
include "syl6bi.mm"
include "com12.mm"
include "rexlimiv.mm"
include "adantl.mm"
include "imp.mm"
include "simpld.mm"
include "simprd.mm"
include "opabex2.mm"
include "cop.mm"
include "wex.mm"
include "elopab.mm"
include "adantld.mm"
include "wb.mm"
include "ad2antrr.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "mpbird.mm"
include "ex.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ssrdv.mm"
include "elpwd.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "sseq2d.mm"
include "ss0b.mm"
include "wal.mm"
include "rex0.mm"
include "rexeq.mm"
include "mtbiri.mm"
include "alrimivv.mm"
include "opab0.mm"
include "sylibr.mm"
include "0elpw.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem sprsymrelfvlem
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cV: class V
  let vc: setvar c
  let vp: setvar p
  let vk: setvar k

  disjoint P c
  disjoint P x
  disjoint P y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint P p
  disjoint c p
  disjoint p x
  disjoint p y
  disjoint V p
  disjoint k x
  assert |- ( P C_ ( Pairs ` V ) -> { <. x , y >. | E. c e. P c = { x , y } } e. ~P ( V X. V ) )

  proof
    cV
    cvv
    wcel
    #
    cP
    cV
    cspr
    cfv
    #
    wss
    #
    vc
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vc
    cP
    wrex
    #
    vx
    vy
    copab
    #
    cV
    cV
    cxp
    #
    cpw
    #
    wcel
    #
    wi
    @0
    @2
    @12
    @0
    @2
    wa
    #
    @9
    @10
    cvv
    @13
    @8
    vx
    vy
    cV
    cV
    cvv
    cvv
    @0
    @2
    simpl
    #
    @14
    @13
    @8
    wa
    #
    @4
    cV
    wcel
    #
    @5
    cV
    wcel
    #
    @13
    @8
    @16
    @17
    wa
    #
    @2
    @8
    @18
    wi
    @0
    @8
    @2
    @18
    @7
    @2
    @18
    wi
    #
    vc
    cP
    @7
    @3
    cP
    wcel
    #
    @19
    @7
    @20
    @6
    cP
    wcel
    #
    @19
    @3
    @6
    cP
    eleq1
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    @21
    @19
    wi
    vx
    vex
    vy
    vex
    @2
    @21
    @22
    @23
    wa
    #
    @18
    @2
    @21
    @24
    @18
    cP
    cvv
    cV
    cvv
    @4
    @5
    prsssprel
    3exp
    com13
    mp2an
    syl6bi
    com12
    rexlimiv
    #
    com12
    adantl
    imp
    #
    simpld
    @15
    @16
    @17
    @26
    simprd
    opabex2
    @13
    vp
    @9
    @10
    vp
    cv
    #
    @9
    wcel
    #
    @13
    @27
    @10
    wcel
    #
    @28
    @27
    @4
    @5
    cop
    #
    wceq
    #
    @8
    wa
    #
    vy
    wex
    vx
    wex
    @13
    @29
    wi
    #
    @8
    vx
    vy
    @27
    elopab
    @32
    @33
    vx
    vy
    @32
    @13
    @29
    @32
    @13
    wa
    #
    @29
    @18
    @32
    @13
    @18
    @32
    @2
    @18
    @0
    @8
    @19
    @31
    @25
    adantl
    adantld
    imp
    @34
    @29
    @30
    @10
    wcel
    #
    @18
    @31
    @29
    @35
    wb
    @8
    @13
    @27
    @30
    @10
    eleq1
    ad2antrr
    @4
    @5
    cV
    cV
    opelxp
    syl6bb
    mpbird
    ex
    exlimivv
    sylbi
    com12
    ssrdv
    elpwd
    ex
    @0
    wn
    #
    @2
    cP
    c0
    wceq
    #
    @12
    @36
    @2
    cP
    c0
    wss
    @37
    @36
    @1
    c0
    cP
    cV
    cspr
    fvprc
    sseq2d
    cP
    ss0b
    syl6bb
    @37
    @9
    c0
    @11
    @37
    @8
    wn
    #
    vy
    wal
    vx
    wal
    @9
    c0
    wceq
    @37
    @38
    vx
    vy
    @37
    @8
    @7
    vc
    c0
    wrex
    @7
    vc
    rex0
    @7
    vc
    cP
    c0
    rexeq
    mtbiri
    alrimivv
    @8
    vx
    vy
    opab0
    sylibr
    @10
    0elpw
    syl6eqel
    syl6bi
    pm2.61i
end
