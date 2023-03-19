include "cv.mm"
include "c5.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cdvds.mm"
include "wn.mm"
include "wi.mm"
include "clt.mm"
include "cr.mm"
include "eluzelre.mm"
include "resqcld.mm"
include "eluzle.mm"
include "cc0.mm"
include "5re.mm"
include "5nn0.mm"
include "nn0ge0i.mm"
include "le2sq2.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "nnrei.mm"
include "resqcli.mm"
include "w3a.mm"
include "cdc.mm"
include "cmul.mm"
include "5cn.mm"
include "sqvali.mm"
include "5t5e25.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "ltletr.mm"
include "mpani.mm"
include "mp3an12.mm"
include "sylc.mm"
include "wb.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "pm2.21d.mm"
include "adantld.mm"
include "adantl.mm"
include "prmlem1a.mm"

theorem prmlem1
  let cN: class N
  let vx: setvar x
  assume prmlem1.n: |- N e. NN
  assume prmlem1.gt: |- 1 < N
  assume prmlem1.2: |- -. 2 || N
  assume prmlem1.3: |- -. 3 || N
  assume prmlem1.lt: |- N < ; 2 5


  assert |- N e. Prime

  proof
    vx
    cN
    prmlem1.n
    prmlem1.gt
    prmlem1.2
    prmlem1.3
    vx
    cv
    #
    c5
    cuz
    cfv
    wcel
    #
    @0
    cprime
    c2
    csn
    cdif
    wcel
    #
    @0
    c2
    cexp
    co
    #
    cN
    cle
    wbr
    #
    wa
    @0
    cN
    cdvds
    wbr
    wn
    #
    wi
    c2
    c5
    cdvds
    wbr
    wn
    @1
    @4
    @5
    @2
    @1
    @4
    @5
    @1
    cN
    @3
    clt
    wbr
    #
    @4
    wn
    #
    @1
    @3
    cr
    wcel
    #
    c5
    c2
    cexp
    co
    #
    @3
    cle
    wbr
    #
    @6
    @1
    @0
    c5
    @0
    eluzelre
    #
    resqcld
    #
    @1
    @0
    cr
    wcel
    #
    c5
    @0
    cle
    wbr
    #
    @10
    @11
    c5
    @0
    eluzle
    c5
    cr
    wcel
    cc0
    c5
    cle
    wbr
    @13
    @14
    wa
    @10
    5re
    c5
    5nn0
    nn0ge0i
    c5
    @0
    le2sq2
    mpanl12
    syl2anc
    cN
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @8
    @10
    @6
    wi
    cN
    prmlem1.n
    nnrei
    #
    c5
    5re
    resqcli
    @15
    @16
    @8
    w3a
    cN
    @9
    clt
    wbr
    @10
    @6
    cN
    c2
    c5
    cdc
    #
    @9
    clt
    prmlem1.lt
    @9
    c5
    c5
    cmul
    co
    @18
    c5
    5cn
    sqvali
    5t5e25
    eqtri
    breqtrri
    cN
    @9
    @3
    ltletr
    mpani
    mp3an12
    sylc
    @1
    @15
    @8
    @6
    @7
    wb
    @17
    @12
    cN
    @3
    ltnle
    sylancr
    mpbid
    pm2.21d
    adantld
    adantl
    prmlem1a
end
