include "ccyg.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cgrp.mm"
include "eqid.mm"
include "iscyg.mm"
include "simprbi.mm"
include "wfo.mm"
include "wa.mm"
include "wfn.mm"
include "ovex.mm"
include "fnmpti.mm"
include "df-fo.mm"
include "mpbiran.mm"
include "ccrd.mm"
include "cdm.mm"
include "wi.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "cen.mm"
include "wb.mm"
include "cn.mm"
include "znnen.mm"
include "nnenom.mm"
include "entri.mm"
include "ennum.mm"
include "mpbir.mm"
include "fodomnum.mm"
include "mp1i.mm"
include "domentr.mm"
include "mpan2.mm"
include "syl6.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem cygctb
  let cB: class B
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
  let cE: class E
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )


  assert |- ( G e. CycGrp -> B ~<_ _om )

  proof
    cG
    ccyg
    wcel
    #
    vn
    cz
    vn
    cv
    #
    vx
    cv
    #
    cG
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    cB
    wceq
    #
    vx
    cB
    wrex
    #
    cB
    com
    cdom
    wbr
    #
    @0
    cG
    cgrp
    wcel
    @7
    vx
    cB
    @3
    vn
    cG
    cygctb.1
    @3
    eqid
    iscyg
    simprbi
    @0
    @6
    @8
    vx
    cB
    @6
    cz
    cB
    @5
    wfo
    #
    @0
    @2
    cB
    wcel
    wa
    #
    @8
    @9
    @5
    cz
    wfn
    @6
    vn
    cz
    @4
    @5
    @1
    @2
    @3
    ovex
    @5
    eqid
    fnmpti
    cz
    cB
    @5
    df-fo
    mpbiran
    @10
    @9
    cB
    cz
    cdom
    wbr
    #
    @8
    cz
    ccrd
    cdm
    #
    wcel
    #
    @9
    @11
    wi
    @10
    @13
    com
    @12
    wcel
    #
    com
    con0
    wcel
    @14
    omelon
    com
    onenon
    ax-mp
    cz
    com
    cen
    wbr
    #
    @13
    @14
    wb
    cz
    cn
    com
    znnen
    nnenom
    entri
    #
    cz
    com
    ennum
    ax-mp
    mpbir
    cz
    cB
    @5
    fodomnum
    mp1i
    @11
    @15
    @8
    @16
    cB
    cz
    com
    domentr
    mpan2
    syl6
    syl5bir
    rexlimdva
    mpd
end
