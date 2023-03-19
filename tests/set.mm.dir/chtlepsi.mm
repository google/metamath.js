include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "cvma.mm"
include "cfv.mm"
include "csu.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "ccht.mm"
include "cchp.mm"
include "cle.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "wbr.mm"
include "vmage0.mm"
include "c2.mm"
include "ppisval.mm"
include "inss1.mm"
include "cuz.mm"
include "wss.mm"
include "2eluzge1.mm"
include "fzss1.mm"
include "mp1i.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "fsumless.mm"
include "clog.mm"
include "chtval.mm"
include "wceq.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "vmaprm.mm"
include "sumeq2dv.mm"
include "eqtr4d.mm"
include "chpval.mm"
include "3brtr4d.mm"

theorem chtlepsi
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cN: class N


  assert |- ( A e. RR -> ( theta ` A ) <_ ( psi ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    vn
    cv
    #
    cvma
    cfv
    #
    vn
    csu
    #
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    @4
    vn
    csu
    cA
    ccht
    cfv
    #
    cA
    cchp
    cfv
    cle
    @0
    @7
    @4
    @2
    vn
    @0
    c1
    @6
    fzfid
    @0
    @3
    @7
    wcel
    #
    wa
    #
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @9
    @11
    @0
    @3
    @6
    elfznn
    adantl
    #
    @3
    vmacl
    syl
    @10
    @11
    cc0
    @4
    cle
    wbr
    @12
    @3
    vmage0
    syl
    @0
    @2
    c2
    @6
    cfz
    co
    #
    cprime
    cin
    #
    @7
    cA
    ppisval
    @0
    @14
    @13
    @7
    @13
    cprime
    inss1
    c2
    c1
    cuz
    cfv
    wcel
    @13
    @7
    wss
    @0
    2eluzge1
    c2
    c1
    @6
    fzss1
    mp1i
    syl5ss
    eqsstrd
    fsumless
    @0
    @8
    @2
    @3
    clog
    cfv
    #
    vn
    csu
    @5
    cA
    vn
    chtval
    @0
    @2
    @4
    @15
    vn
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @3
    cprime
    wcel
    @4
    @15
    wceq
    @17
    @2
    cprime
    @3
    @1
    cprime
    inss2
    @0
    @16
    simpr
    sseldi
    @3
    vmaprm
    syl
    sumeq2dv
    eqtr4d
    cA
    vn
    chpval
    3brtr4d
end
