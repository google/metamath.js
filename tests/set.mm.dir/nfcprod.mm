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
include "nfcri.mm"
include "nfif.mm"
include "nfmpt.mm"
include "nfseq.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfex.mm"
include "nfrex.mm"
include "nf3an.mm"
include "nff1o.mm"
include "nfcsb.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nfor.mm"
include "nfiota.mm"
include "nfcxfr.mm"

theorem nfcprod
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  assume nfcprod.1: |- F/_ x A
  assume nfcprod.2: |- F/_ x B

  disjoint k x
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint k m
  disjoint k n
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B y
  disjoint B z
  assert |- F/_ x prod_ k e. A B

  proof
    vx
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
    vz
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
    #
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
    vz
    wex
    #
    vn
    @1
    wrex
    #
    cmul
    @7
    @0
    cseq
    #
    vy
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
    @15
    @0
    cmul
    vn
    cn
    vk
    @8
    @20
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
    vy
    cio
    vy
    vz
    cA
    cB
    vf
    vk
    vm
    vn
    df-prod
    @31
    vx
    vy
    @18
    @30
    vx
    @17
    vx
    vm
    cz
    vx
    cz
    nfcv
    #
    @2
    @13
    @16
    vx
    vx
    cA
    @1
    nfcprod.1
    vx
    @1
    nfcv
    #
    nfss
    @12
    vx
    vn
    @1
    @33
    @11
    vx
    vz
    @4
    @10
    vx
    @4
    vx
    nfv
    vx
    @9
    @3
    cli
    vx
    cmul
    @7
    @8
    vx
    @8
    nfcv
    vx
    cmul
    nfcv
    #
    vx
    vk
    cz
    @6
    @32
    @5
    vx
    cB
    c1
    vx
    vk
    cA
    nfcprod.1
    nfcri
    nfcprod.2
    vx
    c1
    nfcv
    #
    nfif
    nfmpt
    #
    nfseq
    vx
    cli
    nfcv
    #
    vx
    @3
    nfcv
    nfbr
    nfan
    nfex
    nfrex
    vx
    @14
    @15
    cli
    vx
    cmul
    @7
    @0
    vx
    @0
    nfcv
    #
    @34
    @36
    nfseq
    @37
    vx
    @15
    nfcv
    nfbr
    nf3an
    nfrex
    @29
    vx
    vm
    cn
    vx
    cn
    nfcv
    #
    @28
    vx
    vf
    @21
    @27
    vx
    vx
    @19
    cA
    @20
    vx
    @20
    nfcv
    vx
    @19
    nfcv
    nfcprod.1
    nff1o
    vx
    @15
    @26
    vx
    @0
    @25
    vx
    cmul
    @24
    c1
    @35
    @34
    vx
    vn
    cn
    @23
    @39
    vx
    vk
    @22
    cB
    vx
    @22
    nfcv
    nfcprod.2
    nfcsb
    nfmpt
    nfseq
    @38
    nffv
    nfeq2
    nfan
    nfex
    nfrex
    nfor
    nfiota
    nfcxfr
end
