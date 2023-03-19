include "wcel.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cif.mm"
include "eqidd.mm"
include "wa.mm"
include "simprr.mm"
include "iftrued.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "ad2antrl.mm"
include "eqtrd.mm"
include "elex.mm"
include "0nn0.mm"
include "a1i.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resiexg.mm"
include "syl.mm"
include "ovmpt2d.mm"
include "wb.mm"
include "df-relexp.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem relexp0g
  let cR: class R
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. V -> ( R ^r 0 ) = ( _I |` ( dom R u. ran R ) ) )

  proof
    cR
    cV
    wcel
    #
    cR
    cc0
    crelexp
    co
    #
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    wceq
    #
    wi
    #
    @0
    cR
    cc0
    vr
    vn
    cvv
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    cid
    vr
    cv
    #
    cdm
    #
    @10
    crn
    #
    cun
    #
    cres
    #
    @8
    vx
    vy
    cvv
    cvv
    vx
    cv
    @10
    ccom
    cmpt2
    vz
    cvv
    @10
    cmpt
    c1
    cseq
    cfv
    #
    cif
    #
    cmpt2
    #
    co
    #
    @5
    wceq
    #
    wi
    #
    @0
    vr
    vn
    cR
    cc0
    cvv
    cn0
    @16
    @5
    @17
    cvv
    @0
    @17
    eqidd
    @0
    @10
    cR
    wceq
    #
    @9
    wa
    wa
    #
    @16
    @14
    @5
    @22
    @9
    @14
    @15
    @0
    @21
    @9
    simprr
    iftrued
    @21
    @14
    @5
    wceq
    @0
    @9
    @21
    @13
    @4
    cid
    @21
    @11
    @2
    @12
    @3
    @10
    cR
    dmeq
    @10
    cR
    rneq
    uneq12d
    reseq2d
    ad2antrl
    eqtrd
    cR
    cV
    elex
    cc0
    cn0
    wcel
    @0
    0nn0
    a1i
    @0
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    @0
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @23
    cR
    cV
    dmexg
    cR
    cV
    rnexg
    @2
    @3
    cvv
    cvv
    unexg
    syl2anc
    @4
    cvv
    resiexg
    syl
    ovmpt2d
    crelexp
    @17
    wceq
    #
    @7
    @20
    wb
    vx
    vy
    vz
    vn
    vr
    df-relexp
    @24
    @6
    @19
    @0
    @24
    @1
    @18
    @5
    cR
    cc0
    crelexp
    @17
    oveq
    eqeq1d
    imbi2d
    ax-mp
    mpbir
end
