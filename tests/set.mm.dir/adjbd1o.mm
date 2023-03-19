include "cbo.mm"
include "cado.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cdm.mm"
include "wf1.mm"
include "wss.mm"
include "adj1o.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "bdopssadj.mm"
include "f1ores.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wrex.mm"
include "cfv.mm"
include "vex.mm"
include "elima.mm"
include "wfn.mm"
include "f1ofn.mm"
include "bdopadj.mm"
include "fnbrfvb.mm"
include "sylancr.mm"
include "rexbiia.mm"
include "adjbdlnb.mm"
include "eleq1.mm"
include "syl5bb.mm"
include "biimpcd.mm"
include "rexlimiv.mm"
include "adjbdln.mm"
include "adjadj.mm"
include "syl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "impbii.mm"
include "3bitr2i.mm"
include "eqriv.mm"
include "f1oeq3.mm"
include "mpbi.mm"

theorem adjbd1o
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- ( adjh |` BndLinOp ) : BndLinOp -1-1-onto-> BndLinOp

  proof
    cbo
    cado
    cbo
    cima
    #
    cado
    cbo
    cres
    #
    wf1o
    #
    cbo
    cbo
    @1
    wf1o
    #
    cado
    cdm
    #
    @4
    cado
    wf1
    #
    cbo
    @4
    wss
    @2
    @4
    @4
    cado
    wf1o
    #
    @5
    adj1o
    @4
    @4
    cado
    f1of1
    ax-mp
    bdopssadj
    @4
    @4
    cbo
    cado
    f1ores
    mp2an
    @0
    cbo
    wceq
    @2
    @3
    wb
    vy
    @0
    cbo
    vy
    cv
    #
    @0
    wcel
    vx
    cv
    #
    @7
    cado
    wbr
    #
    vx
    cbo
    wrex
    @8
    cado
    cfv
    #
    @7
    wceq
    #
    vx
    cbo
    wrex
    #
    @7
    cbo
    wcel
    #
    vx
    @7
    cado
    cbo
    vy
    vex
    elima
    @11
    @9
    vx
    cbo
    @8
    cbo
    wcel
    #
    cado
    @4
    wfn
    #
    @8
    @4
    wcel
    @11
    @9
    wb
    @6
    @15
    adj1o
    @4
    @4
    cado
    f1ofn
    ax-mp
    @8
    bdopadj
    @4
    @8
    @7
    cado
    fnbrfvb
    sylancr
    rexbiia
    @12
    @13
    @11
    @13
    vx
    cbo
    @11
    @14
    @13
    @14
    @10
    cbo
    wcel
    @11
    @13
    @8
    adjbdlnb
    @10
    @7
    cbo
    eleq1
    syl5bb
    biimpcd
    rexlimiv
    @13
    @7
    cado
    cfv
    #
    cbo
    wcel
    @16
    cado
    cfv
    #
    @7
    wceq
    #
    @12
    @7
    adjbdln
    @13
    @7
    @4
    wcel
    @18
    @7
    bdopadj
    @7
    adjadj
    syl
    @11
    @18
    vx
    @16
    cbo
    @8
    @16
    wceq
    @10
    @17
    @7
    @8
    @16
    cado
    fveq2
    eqeq1d
    rspcev
    syl2anc
    impbii
    3bitr2i
    eqriv
    @0
    cbo
    cbo
    @1
    f1oeq3
    ax-mp
    mpbi
end
