include "cfmtno.mm"
include "crn.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cn0.mm"
include "cn.mm"
include "wf1.mm"
include "wf.mm"
include "fmtnof1.mm"
include "f1f.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "wss.mm"
include "nnssnn0.mm"
include "nnnfi.mm"
include "ssfi.mm"
include "expcom.mm"
include "con3d.mm"
include "mp2.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "syl.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "fundmfibi.mm"
include "mtbird.mm"
include "mp2b.mm"
include "cvv.mm"
include "nn0ex.mm"
include "wa.mm"
include "f1dmvrnfibi.mm"
include "notbid.mm"
include "mp2an.mm"
include "mpbi.mm"
include "nelir.mm"

theorem fmtnoinf
  let vk: setvar k
  let vx: setvar x


  assert |- ran FermatNo e/ Fin

  proof
    cfmtno
    crn
    #
    cfn
    cfmtno
    cfn
    wcel
    #
    wn
    #
    @0
    cfn
    wcel
    #
    wn
    #
    cn0
    cn
    cfmtno
    wf1
    #
    cn0
    cn
    cfmtno
    wf
    #
    @2
    fmtnof1
    cn0
    cn
    cfmtno
    f1f
    @6
    @1
    cfmtno
    cdm
    #
    cfn
    wcel
    #
    @6
    @7
    cn0
    wceq
    #
    @8
    wn
    cn0
    cn
    cfmtno
    fdm
    @9
    @8
    cn0
    cfn
    wcel
    #
    cn
    cn0
    wss
    #
    cn
    cfn
    wcel
    #
    wn
    @10
    wn
    nnssnn0
    nnnfi
    @11
    @10
    @12
    @10
    @11
    @12
    cn0
    cn
    ssfi
    expcom
    con3d
    mp2
    @7
    cn0
    cfn
    eleq1
    mtbiri
    syl
    @6
    cfmtno
    wfun
    @1
    @8
    wb
    cn0
    cn
    cfmtno
    ffun
    cfmtno
    fundmfibi
    syl
    mtbird
    mp2b
    cn0
    cvv
    wcel
    #
    @5
    @2
    @4
    wb
    nn0ex
    fmtnof1
    @13
    @5
    wa
    @1
    @3
    cn0
    cn
    cfmtno
    cvv
    f1dmvrnfibi
    notbid
    mp2an
    mpbi
    nelir
end
