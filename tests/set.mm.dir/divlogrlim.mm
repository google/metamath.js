include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "clt.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wb.mm"
include "wtru.mm"
include "cc.mm"
include "wcel.mm"
include "elioore.mm"
include "eliooord.mm"
include "simpld.mm"
include "rplogcld.mm"
include "rprecred.mm"
include "recnd.mm"
include "rgen.mm"
include "a1i.mm"
include "wss.mm"
include "ioossre.mm"
include "rlim0lt.mm"
include "trud.mm"
include "ce.mm"
include "id.mm"
include "reefcld.mm"
include "wa.mm"
include "ad2antlr.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "absidd.mm"
include "simpll.mm"
include "simpr.mm"
include "1rp.mm"
include "rpred.mm"
include "ltled.mm"
include "rpgecld.mm"
include "reeflogd.mm"
include "breqtrrd.mm"
include "eflt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ltrec1d.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mprgbir.mm"

theorem divlogrlim
  let vx: setvar x
  let vc: setvar c
  let vy: setvar y


  assert |- ( x e. ( 1 (,) +oo ) |-> ( 1 / ( log ` x ) ) ) ~~>r 0

  proof
    vx
    c1
    cpnf
    cioo
    co
    #
    c1
    vx
    cv
    #
    clog
    cfv
    #
    cdiv
    co
    #
    cmpt
    cc0
    crli
    wbr
    #
    vc
    cv
    #
    @1
    clt
    wbr
    #
    @3
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    @0
    wral
    #
    vc
    cr
    wrex
    #
    vy
    crp
    @4
    @12
    vy
    crp
    wral
    wb
    wtru
    vy
    vc
    vx
    @0
    @3
    @3
    cc
    wcel
    #
    vx
    @0
    wral
    wtru
    @13
    vx
    @0
    @1
    @0
    wcel
    #
    @3
    @14
    @2
    @14
    @1
    @1
    c1
    cpnf
    elioore
    #
    @14
    c1
    @1
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    @1
    c1
    cpnf
    eliooord
    simpld
    #
    rplogcld
    #
    rprecred
    #
    recnd
    rgen
    a1i
    @0
    cr
    wss
    wtru
    c1
    cpnf
    ioossre
    a1i
    rlim0lt
    trud
    @8
    crp
    wcel
    #
    c1
    @8
    cdiv
    co
    #
    ce
    cfv
    #
    cr
    wcel
    @22
    @1
    clt
    wbr
    #
    @9
    wi
    #
    vx
    @0
    wral
    #
    @12
    @20
    @21
    @20
    @8
    @20
    id
    rprecred
    reefcld
    @20
    @24
    vx
    @0
    @20
    @14
    wa
    #
    @23
    @9
    @26
    @23
    wa
    #
    @7
    @3
    @8
    clt
    @27
    @3
    @14
    @3
    cr
    wcel
    @20
    @23
    @19
    ad2antlr
    @27
    @3
    @27
    @2
    @27
    @1
    @14
    @1
    cr
    wcel
    @20
    @23
    @15
    ad2antlr
    #
    @14
    @16
    @20
    @23
    @17
    ad2antlr
    #
    rplogcld
    rpreccld
    rpge0d
    absidd
    @27
    @8
    @2
    @20
    @14
    @23
    simpll
    #
    @14
    @2
    crp
    wcel
    @20
    @23
    @18
    ad2antlr
    #
    @27
    @21
    @2
    clt
    wbr
    #
    @22
    @2
    ce
    cfv
    #
    clt
    wbr
    #
    @27
    @22
    @1
    @33
    clt
    @26
    @23
    simpr
    @27
    @1
    @27
    @1
    c1
    @28
    c1
    crp
    wcel
    @27
    1rp
    a1i
    #
    @27
    c1
    @1
    @27
    c1
    @35
    rpred
    @28
    @29
    ltled
    rpgecld
    reeflogd
    breqtrrd
    @27
    @21
    cr
    wcel
    @2
    cr
    wcel
    @32
    @34
    wb
    @27
    @8
    @30
    rprecred
    @27
    @2
    @31
    rpred
    @21
    @2
    eflt
    syl2anc
    mpbird
    ltrec1d
    eqbrtrd
    ex
    ralrimiva
    @11
    @25
    vc
    @22
    cr
    @5
    @22
    wceq
    #
    @10
    @24
    vx
    @0
    @36
    @6
    @23
    @9
    @5
    @22
    @1
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    mprgbir
end
