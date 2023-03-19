include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "csu.mm"
include "wceq.mm"
include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "caddc.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cli.mm"
include "eqid.mm"
include "simpr.mm"
include "simpl.mm"
include "cv.mm"
include "cif.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "ifid.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "0cnd.mm"
include "zsum.mm"
include "wfun.mm"
include "wbr.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "fclim.mm"
include "ffun.mm"
include "ax-mp.mm"
include "serclim0.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "cpw.mm"
include "uzf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "sseq2d.mm"
include "biimpac.mm"
include "ss0.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "3syl.mm"
include "pm2.61dan.mm"
include "chash.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wex.mm"
include "wo.mm"
include "fz1f1o.mm"
include "eqidd.mm"
include "elfznn.mm"
include "syl.mm"
include "fsum.mm"
include "nnuz.mm"
include "ser0.mm"
include "adantr.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "jaoi.mm"

theorem sumz
  let cA: class A
  let vk: setvar k
  let cM: class M
  let vf: setvar f
  let vn: setvar n

  disjoint A k
  disjoint M k
  disjoint f k
  disjoint f n
  disjoint A f
  disjoint k n
  disjoint A n
  assert |- ( ( A C_ ( ZZ>= ` M ) \/ A e. Fin ) -> sum_ k e. A 0 = 0 )

  proof
    cA
    cM
    cuz
    cfv
    #
    wss
    #
    cA
    cc0
    vk
    csu
    #
    cc0
    wceq
    #
    cA
    cfn
    wcel
    #
    @1
    cM
    cz
    wcel
    #
    @3
    @1
    @5
    wa
    #
    @2
    caddc
    @0
    cc0
    csn
    #
    cxp
    #
    cM
    cseq
    #
    cli
    cfv
    #
    cc0
    @6
    cA
    cc0
    vk
    @8
    cM
    @0
    @0
    eqid
    @1
    @5
    simpr
    @1
    @5
    simpl
    vk
    cv
    #
    @0
    wcel
    #
    @11
    @8
    cfv
    #
    @11
    cA
    wcel
    #
    cc0
    cc0
    cif
    #
    wceq
    @6
    @12
    @13
    cc0
    @15
    @0
    cc0
    @11
    c0ex
    fvconst2
    @14
    cc0
    ifid
    syl6eqr
    adantl
    @6
    @14
    wa
    0cnd
    zsum
    cli
    wfun
    #
    @6
    @9
    cc0
    cli
    wbr
    #
    @10
    cc0
    wceq
    cli
    cdm
    #
    cc
    cli
    wf
    @16
    fclim
    @18
    cc
    cli
    ffun
    ax-mp
    @5
    @17
    @1
    cM
    serclim0
    adantl
    @9
    cc0
    cli
    funbrfv
    mpsyl
    eqtrd
    @1
    @5
    wn
    #
    wa
    cA
    c0
    wss
    #
    cA
    c0
    wceq
    #
    @3
    @19
    @1
    @20
    @19
    @0
    c0
    cA
    @5
    cM
    cuz
    cdm
    #
    wcel
    @0
    c0
    wceq
    @22
    cz
    cM
    cz
    cz
    cpw
    cuz
    uzf
    fdmi
    eleq2i
    cM
    cuz
    ndmfv
    sylnbir
    sseq2d
    biimpac
    cA
    ss0
    @21
    @2
    c0
    cc0
    vk
    csu
    cc0
    cA
    c0
    cc0
    vk
    sumeq1
    cc0
    vk
    sum0
    syl6eq
    #
    3syl
    pm2.61dan
    @4
    @21
    cA
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @24
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    wo
    @3
    cA
    vf
    fz1f1o
    @21
    @3
    @30
    @23
    @25
    @29
    @3
    @25
    @28
    @3
    vf
    @25
    @28
    @3
    @25
    @28
    wa
    #
    @2
    @24
    caddc
    cn
    @7
    cxp
    #
    c1
    cseq
    cfv
    #
    cc0
    @31
    cA
    cc0
    cc0
    vk
    vn
    @27
    @32
    @24
    @11
    vn
    cv
    #
    @27
    cfv
    wceq
    cc0
    eqidd
    @25
    @28
    simpl
    @25
    @28
    simpr
    @31
    @14
    wa
    0cnd
    @34
    @26
    wcel
    #
    @34
    @32
    cfv
    cc0
    wceq
    #
    @31
    @35
    @34
    cn
    wcel
    @36
    @34
    @24
    elfznn
    cn
    cc0
    @34
    c0ex
    fvconst2
    syl
    adantl
    fsum
    @25
    @33
    cc0
    wceq
    @28
    c1
    @24
    cn
    nnuz
    ser0
    adantr
    eqtrd
    ex
    exlimdv
    imp
    jaoi
    syl
    jaoi
end
