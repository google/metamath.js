include "cprod.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "csb.mm"
include "wceq.mm"
include "wo.mm"
include "cio.mm"
include "df-prod.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfseq.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfex.mm"
include "nfrex.mm"
include "nf3an.mm"
include "nff1o.mm"
include "nfcsb1v.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nfor.mm"
include "nfiota.mm"
include "nfcxfr.mm"

theorem nfcprod1
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume nfcprod1.1: |- F/_ k A

  disjoint A k
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  assert |- F/_ k prod_ k e. A B

  proof
    vk
    cA
    cB
    vk
    cprod
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    vk
    cz
    vk
    cv
    cA
    wcel
    cB
    c1
    cif
    #
    cmpt
    #
    vn
    cv
    #
    cseq
    #
    @3
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @1
    wrex
    #
    cmul
    @6
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    c1
    @0
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @14
    @0
    cmul
    vn
    cn
    vk
    @7
    @19
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    vx
    vy
    cA
    cB
    vf
    vk
    vm
    vn
    df-prod
    @30
    vk
    vx
    @17
    @29
    vk
    @16
    vk
    vm
    cz
    vk
    cz
    nfcv
    @2
    @12
    @15
    vk
    vk
    cA
    @1
    nfcprod1.1
    vk
    @1
    nfcv
    #
    nfss
    @11
    vk
    vn
    @1
    @31
    @10
    vk
    vy
    @4
    @9
    vk
    @4
    vk
    nfv
    vk
    @8
    @3
    cli
    vk
    cmul
    @6
    @7
    vk
    @7
    nfcv
    vk
    cmul
    nfcv
    #
    vk
    cz
    @5
    nfmpt1
    #
    nfseq
    vk
    cli
    nfcv
    #
    vk
    @3
    nfcv
    nfbr
    nfan
    nfex
    nfrex
    vk
    @13
    @14
    cli
    vk
    cmul
    @6
    @0
    vk
    @0
    nfcv
    #
    @32
    @33
    nfseq
    @34
    vk
    @14
    nfcv
    nfbr
    nf3an
    nfrex
    @28
    vk
    vm
    cn
    vk
    cn
    nfcv
    #
    @27
    vk
    vf
    @20
    @26
    vk
    vk
    @18
    cA
    @19
    vk
    @19
    nfcv
    vk
    @18
    nfcv
    nfcprod1.1
    nff1o
    vk
    @14
    @25
    vk
    @0
    @24
    vk
    cmul
    @23
    c1
    vk
    c1
    nfcv
    @32
    vk
    vn
    cn
    @22
    @36
    vk
    @21
    cB
    nfcsb1v
    nfmpt
    nfseq
    @35
    nffv
    nfeq2
    nfan
    nfex
    nfrex
    nfor
    nfiota
    nfcxfr
end
