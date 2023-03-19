include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c1.mm"
include "cprod.mm"
include "wceq.mm"
include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "simpr.mm"
include "cc0.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "prodfclim1.mm"
include "adantl.mm"
include "simpl.mm"
include "cv.mm"
include "cif.mm"
include "1ex.mm"
include "fvconst2.mm"
include "ifid.mm"
include "syl6eqr.mm"
include "1cnd.mm"
include "zprodn0.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "cpw.mm"
include "uzf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "sseq2d.mm"
include "biimpac.mm"
include "ss0.mm"
include "prodeq1.mm"
include "prod0.mm"
include "syl6eq.mm"
include "3syl.mm"
include "pm2.61dan.mm"
include "chash.mm"
include "cn.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wex.mm"
include "wo.mm"
include "fz1f1o.mm"
include "eqidd.mm"
include "elfznn.mm"
include "syl.mm"
include "fprod.mm"
include "nnuz.mm"
include "prodf1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "jaoi.mm"

theorem prod1
  let cA: class A
  let vk: setvar k
  let cM: class M
  let vf: setvar f
  let vj: setvar j

  disjoint A k
  disjoint M k
  disjoint A f
  disjoint A j
  disjoint f j
  disjoint f k
  disjoint j k
  assert |- ( ( A C_ ( ZZ>= ` M ) \/ A e. Fin ) -> prod_ k e. A 1 = 1 )

  proof
    cA
    cM
    cuz
    cfv
    #
    wss
    #
    cA
    c1
    vk
    cprod
    #
    c1
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
    cA
    c1
    vk
    @0
    c1
    csn
    #
    cxp
    #
    cM
    c1
    @0
    @0
    eqid
    #
    @1
    @5
    simpr
    c1
    cc0
    wne
    @6
    ax-1ne0
    a1i
    @5
    cmul
    @8
    cM
    cseq
    c1
    cli
    wbr
    @1
    cM
    @0
    @9
    prodfclim1
    adantl
    @1
    @5
    simpl
    vk
    cv
    #
    @0
    wcel
    #
    @10
    @8
    cfv
    #
    @10
    cA
    wcel
    #
    c1
    c1
    cif
    #
    wceq
    @6
    @11
    @12
    c1
    @14
    @0
    c1
    @10
    1ex
    fvconst2
    @13
    c1
    ifid
    syl6eqr
    adantl
    @6
    @13
    wa
    1cnd
    zprodn0
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
    @15
    @1
    @16
    @15
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
    @18
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
    @17
    @2
    c0
    c1
    vk
    cprod
    c1
    cA
    c0
    c1
    vk
    prodeq1
    c1
    vk
    prod0
    syl6eq
    #
    3syl
    pm2.61dan
    @4
    @17
    cA
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @20
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
    @17
    @3
    @26
    @19
    @21
    @25
    @3
    @21
    @24
    @3
    vf
    @21
    @24
    @3
    @21
    @24
    wa
    #
    @2
    @20
    cmul
    cn
    @7
    cxp
    #
    c1
    cseq
    cfv
    #
    c1
    @27
    cA
    c1
    c1
    vk
    vj
    @23
    @28
    @20
    @10
    vj
    cv
    #
    @23
    cfv
    wceq
    c1
    eqidd
    @21
    @24
    simpl
    @21
    @24
    simpr
    @27
    @13
    wa
    1cnd
    @30
    @22
    wcel
    #
    @30
    @28
    cfv
    c1
    wceq
    #
    @27
    @31
    @30
    cn
    wcel
    @32
    @30
    @20
    elfznn
    cn
    c1
    @30
    1ex
    fvconst2
    syl
    adantl
    fprod
    @21
    @29
    c1
    wceq
    @24
    c1
    @20
    cn
    nnuz
    prodf1
    adantr
    eqtrd
    ex
    exlimdv
    imp
    jaoi
    syl
    jaoi
end
