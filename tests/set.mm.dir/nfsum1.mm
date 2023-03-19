include "csu.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "csb.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "wceq.mm"
include "wex.mm"
include "wo.mm"
include "cio.mm"
include "df-sum.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfcri.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "nfmpt.mm"
include "nfseq.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfrex.mm"
include "nff1o.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nfex.mm"
include "nfor.mm"
include "nfiota.mm"
include "nfcxfr.mm"

theorem nfsum1
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume nfsum1.1: |- F/_ k A


  assert |- F/_ k sum_ k e. A B

  proof
    vk
    cA
    cB
    vk
    csu
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    caddc
    vn
    cz
    vn
    cv
    #
    cA
    wcel
    #
    vk
    @3
    cB
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    wa
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
    @9
    @0
    caddc
    vn
    cn
    vk
    @3
    @14
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
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    @25
    vk
    vx
    @12
    @24
    vk
    @11
    vk
    vm
    cz
    vk
    cz
    nfcv
    #
    @2
    @10
    vk
    vk
    cA
    @1
    nfsum1.1
    vk
    @1
    nfcv
    nfss
    vk
    @8
    @9
    cli
    vk
    caddc
    @7
    @0
    vk
    @0
    nfcv
    #
    vk
    caddc
    nfcv
    #
    vk
    vn
    cz
    @6
    @26
    @4
    vk
    @5
    cc0
    vk
    vn
    cA
    nfsum1.1
    nfcri
    vk
    @3
    cB
    nfcsb1v
    vk
    cc0
    nfcv
    nfif
    nfmpt
    nfseq
    vk
    cli
    nfcv
    vk
    @9
    nfcv
    nfbr
    nfan
    nfrex
    @23
    vk
    vm
    cn
    vk
    cn
    nfcv
    #
    @22
    vk
    vf
    @15
    @21
    vk
    vk
    @13
    cA
    @14
    vk
    @14
    nfcv
    vk
    @13
    nfcv
    nfsum1.1
    nff1o
    vk
    @9
    @20
    vk
    @0
    @19
    vk
    caddc
    @18
    c1
    vk
    c1
    nfcv
    @28
    vk
    vn
    cn
    @17
    @29
    vk
    @16
    cB
    nfcsb1v
    nfmpt
    nfseq
    @27
    nffv
    nfeq2
    nfan
    nfex
    nfrex
    nfor
    nfiota
    nfcxfr
end
