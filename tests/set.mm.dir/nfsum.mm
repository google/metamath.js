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
include "nfcsb.mm"
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

theorem nfsum
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  assume nfsum.1: |- F/_ x A
  assume nfsum.2: |- F/_ x B


  assert |- F/_ x sum_ k e. A B

  proof
    vx
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
    vz
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
    vz
    cio
    vz
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    @25
    vx
    vz
    @12
    @24
    vx
    @11
    vx
    vm
    cz
    vx
    cz
    nfcv
    #
    @2
    @10
    vx
    vx
    cA
    @1
    nfsum.1
    vx
    @1
    nfcv
    nfss
    vx
    @8
    @9
    cli
    vx
    caddc
    @7
    @0
    vx
    @0
    nfcv
    #
    vx
    caddc
    nfcv
    #
    vx
    vn
    cz
    @6
    @26
    @4
    vx
    @5
    cc0
    vx
    vn
    cA
    nfsum.1
    nfcri
    vx
    vk
    @3
    cB
    vx
    @3
    nfcv
    nfsum.2
    nfcsb
    vx
    cc0
    nfcv
    nfif
    nfmpt
    nfseq
    vx
    cli
    nfcv
    vx
    @9
    nfcv
    nfbr
    nfan
    nfrex
    @23
    vx
    vm
    cn
    vx
    cn
    nfcv
    #
    @22
    vx
    vf
    @15
    @21
    vx
    vx
    @13
    cA
    @14
    vx
    @14
    nfcv
    vx
    @13
    nfcv
    nfsum.1
    nff1o
    vx
    @9
    @20
    vx
    @0
    @19
    vx
    caddc
    @18
    c1
    vx
    c1
    nfcv
    @28
    vx
    vn
    cn
    @17
    @29
    vx
    vk
    @16
    cB
    vx
    @16
    nfcv
    nfsum.2
    nfcsb
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
